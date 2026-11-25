use crate::contracts::graph::evidence::Evidence;
use crate::contracts::graph::sets::{Combination, Cursor, SetId};
use crate::contracts::graph::summaries::CallNode;
use crate::contracts::graph::{CapacityError, ConditionId, ExprId, Graph, NodeId, TargetNode};
use crate::contracts::{CheckBasis, Invocation, Writes};
use crate::sequence::Sequence;
use crate::values::{self, Values};
use rustc_hir::def_id::DefId;
use std::ops::Index;

macro_rules! set_index {
    ($value:ty, $field:ident) => {
        impl<'g> Index<SetId<'g, $value>> for Graph<'g> {
            type Output = crate::contracts::graph::sets::Node<'g, $value>;
            fn index(&self, set: SetId<'g, $value>) -> &Self::Output {
                &self.$field[set]
            }
        }
    };
}
set_index!(usize, input_sets);
set_index!(DefId, function_sets);
set_index!(NodeId<'g>, reference_sets);

impl<'g> AsRef<Values<'g>> for Graph<'g> {
    fn as_ref(&self) -> &Values<'g> {
        &self.values
    }
}

impl<'g> Graph<'g> {
    pub(crate) fn members<T: Copy + Eq + std::hash::Hash + 'g>(
        &self,
        set: SetId<'g, T>,
    ) -> impl Iterator<Item = T> + '_
    where
        Self: Index<SetId<'g, T>, Output = crate::contracts::graph::sets::Node<'g, T>>,
    {
        let mut cursor = Cursor::from(set);
        std::iter::from_fn(move || cursor.next(self))
    }

    pub(crate) fn independent_arguments(
        &mut self,
        left: SetId<'g, usize>,
        right: SetId<'g, usize>,
    ) -> Result<Option<()>, CapacityError> {
        let intersection = self
            .input_sets
            .combine(Combination::Intersection, left, right)?;
        Ok((intersection == SetId::EMPTY).then_some(()))
    }

    pub(crate) fn record_argument_write(
        &mut self,
        writes: &mut Writes<'g>,
        position: usize,
    ) -> Result<(), CapacityError> {
        let argument = self.input_sets.insert(SetId::EMPTY, position)?;
        writes.merge(&Writes::Arguments(argument), self)
    }

    pub(crate) fn include_guard(
        &mut self,
        members: &mut SetId<'g, ConditionId<'g>>,
        condition: ConditionId<'g>,
    ) -> Result<Option<()>, CapacityError> {
        if let Some(()) = self.guard_member_sets.contains(*members, condition) {
            return Ok(None);
        }
        *members = self.guard_member_sets.insert(*members, condition)?;
        Ok(Some(()))
    }

    pub(crate) fn combine_evidence(
        &mut self,
        operation: Combination,
        left: Evidence<'g>,
        right: Evidence<'g>,
    ) -> Result<Evidence<'g>, CapacityError> {
        let conditions = self.guard_member_sets.combine(operation, left.0, right.0)?;
        Ok(Evidence(conditions))
    }
}

macro_rules! value_index {
    ($id:ident, $output:ty) => {
        impl<'g> Index<values::$id<'g>> for Graph<'g> {
            type Output = $output;
            fn index(&self, id: values::$id<'g>) -> &Self::Output {
                &self.values[id]
            }
        }
    };
}
value_index!(TextId, str);
value_index!(TypeId, values::TypeNode<'g>);
value_index!(GenericId, values::GenericNode<'g>);
value_index!(InstanceId, values::InstanceNode<'g>);
value_index!(OriginId, values::OriginNode<'g>);

impl<'g, T> values::StoreValue<T> for Graph<'g>
where
    Values<'g>: values::StoreValue<T>,
{
    type Id = <Values<'g> as values::StoreValue<T>>::Id;
    fn intern_value(&mut self, value: T) -> Result<Self::Id, CapacityError> {
        self.values.intern_value(value)
    }
}

impl<'g> Graph<'g> {
    pub(crate) fn unsupported_consumer(
        &mut self,
        def: DefId,
        span: rustc_span::Span,
        reason: &str,
    ) -> Result<crate::contracts::summaries::ConsumerId<'g>, CapacityError> {
        let reason = self.values.intern_text(reason)?;
        self.summaries
            .intern_consumer(crate::contracts::summaries::ConsumerNode {
                def,
                span,
                operation: crate::contracts::summaries::OperationNode::Unsupported(reason),
            })
    }

    pub(crate) fn origin_local(
        &self,
        id: values::OriginId<'g>,
    ) -> Option<rustc_middle::mir::Local> {
        let identity = self.values[self.values[id].identity?];
        Some(
            self.values
                .iter(identity.calls)
                .next()
                .unwrap_or(identity.origin)
                .1,
        )
    }

    pub(crate) fn substitute_call(
        &mut self,
        call: &CallNode<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        invocation: &Invocation<'g>,
    ) -> Result<CallNode<'g>, CapacityError> {
        let target = match call.target {
            TargetNode::Direct(instance) => TargetNode::Direct(
                self.values
                    .substitute_instance(instance, invocation.generics)?,
            ),
            TargetNode::Indirect(value) => {
                TargetNode::Indirect(self.substitute_expr(value, arguments, invocation)?)
            }
        };
        Ok(CallNode {
            basis: match &call.basis {
                CheckBasis::Expression => CheckBasis::Expression,
                CheckBasis::ControlFlow(basis) => {
                    CheckBasis::ControlFlow(self.substitute_guards(basis, arguments, invocation)?)
                }
            },
            target,
            arguments: self.substitute_arguments(&call.arguments, arguments, invocation)?,
            guards: self.substitute_guards(&call.guards, arguments, invocation)?,
            span: call.span,
        })
    }

    pub(crate) fn specialize_receiver(
        &mut self,
        instance: &mut values::InstanceNode<'g>,
        ty: values::TypeId<'g>,
    ) -> Result<Option<()>, CapacityError> {
        let first = self.values.iter(instance.args).next();
        let Some(first) = first else {
            return Ok(None);
        };
        let values::GenericNode::Type(_) = self.values[first] else {
            return Ok(None);
        };
        let replacement = self.values.intern(values::GenericNode::Type(ty))?;
        instance.args = self
            .values
            .replace_generic(instance.args, 0, replacement)?
            .expect("receiver generic exists");
        Ok(Some(()))
    }

    pub(crate) fn instance_with_args(
        &mut self,
        def: DefId,
        args: impl IntoIterator<Item = values::GenericId<'g>>,
        dispatch: values::Dispatch,
    ) -> Result<values::InstanceId<'g>, CapacityError> {
        let args = self.values.intern_list::<values::GenericsId<'g>>(args)?;
        self.values.intern(values::InstanceNode {
            def,
            args,
            dispatch,
        })
    }
}

impl<'g> crate::contracts::ArgumentUnion<'g> for Graph<'g> {
    fn union_arguments(
        &mut self,
        left: SetId<'g, usize>,
        right: SetId<'g, usize>,
    ) -> Result<SetId<'g, usize>, CapacityError> {
        self.input_sets.union_arguments(left, right)
    }
}
