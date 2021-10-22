use rustc_middle::mir;
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{self, Ty, TypeFoldable};
use rustc_span::source_map::Spanned;

pub(crate) trait NeighborSourceKind<'tcx>: TypeFoldable<'tcx> + Clone + Copy {
    fn as_source(self) -> NeighborSource<'tcx>;
}

macro_rules! neighbor_source {
(
    $NeighborSource:ident<$tcx:lifetime>  {
        $(
            $variant:ident
            $(($($tuple_ty:ty),*))?
            $({
                $($name:ident: $struct_ty:ty),*$(,)?
            })?
        ),*$(,)?
    }
) => {
        #[derive(Debug, TypeFoldable, Clone, Copy)]
        pub(crate) enum $NeighborSource<$tcx> {
            Concrete,
            $($variant($variant<$tcx>)),*
        }

        #[derive(Debug, TypeFoldable, Clone, Copy)]
        pub(crate) struct Concrete;
        impl<$tcx> NeighborSourceKind<$tcx> for Concrete {
            fn as_source(self) -> $NeighborSource<$tcx> {
                $NeighborSource::Concrete
            }
        }


        $(
            #[derive(Debug, TypeFoldable, Clone, Copy)]
            pub(crate) struct $variant<$tcx>
            $(($(pub(crate) $tuple_ty),*);)?
            $({
                $(pub(crate) $name: $struct_ty),*
            })?

            impl<$tcx> NeighborSourceKind<$tcx> for $variant<$tcx> {
                fn as_source(self) -> $NeighborSource<$tcx> {
                    $NeighborSource::$variant(self)
                }
            }
        )*

    };
}

neighbor_source! {
    NeighborSource<'tcx> {
        // Concrete -- part of the macro itself as other variants use `'tcx`.
        PointerUnsize {
            target_ty: Ty<'tcx>,
            source_ty: Ty<'tcx>,
        },
        ReifyFnPointer(Ty<'tcx>),
        ClosureFnPointer(Ty<'tcx>),
        MirConstant(mir::ConstantKind<'tcx>),
        TyConstant(&'tcx ty::Const<'tcx>),
        Function(Ty<'tcx>),
        IndirectFunction(Ty<'tcx>),
        DropType(Ty<'tcx>),
    }
}

#[derive(Debug, Clone)]
pub(crate) enum NeighborKind<'tcx> {
    CodegenLocally(Spanned<MonoItem<'tcx>>),
    /// FIXME(polymorphization): Figure out
    /// why we're not doing any local codegen for
    /// this neighbor so that this doesn't
    /// completely inhibit polymorphization.
    NoLocalCodegen,
}

#[derive(Debug, Clone)]
pub(crate) struct Neighbor<'tcx> {
    pub(crate) source: NeighborSource<'tcx>,
    pub(crate) kind: NeighborKind<'tcx>,
}

impl Neighbor<'tcx> {
    pub(crate) fn codegen_locally_item_mut(&mut self) -> Option<&mut Spanned<MonoItem<'tcx>>> {
        match self.kind {
            NeighborKind::CodegenLocally(ref mut item) => Some(item),
            NeighborKind::NoLocalCodegen => None,
        }
    }

    pub(crate) fn codegen_locally_item(&self) -> Option<&Spanned<MonoItem<'tcx>>> {
        match self.kind {
            NeighborKind::CodegenLocally(ref item) => Some(item),
            NeighborKind::NoLocalCodegen => None,
        }
    }
}
