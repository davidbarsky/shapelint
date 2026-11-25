use crate::contracts::Writes;
use crate::contracts::graph::evidence::Evidence;
use crate::contracts::graph::sets::{Combination, Cursor, SetId};
use crate::contracts::graph::{CapacityError, Graph, NodeId};
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

    pub(crate) fn record_argument_write(
        &mut self,
        writes: &mut Writes<'g>,
        position: usize,
    ) -> Result<(), CapacityError> {
        let argument = self.input_sets.insert(SetId::EMPTY, position)?;
        writes.merge(&Writes::Arguments(argument), self)
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
