use crate::contracts::graph::sets::SetId;
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

impl<'g> Graph<'g> {}

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

impl<'g> Graph<'g> {}

impl<'g> crate::contracts::ArgumentUnion<'g> for Graph<'g> {
    fn union_arguments(
        &mut self,
        left: SetId<'g, usize>,
        right: SetId<'g, usize>,
    ) -> Result<SetId<'g, usize>, CapacityError> {
        self.input_sets.union_arguments(left, right)
    }
}
