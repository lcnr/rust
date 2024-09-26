use std::hash::Hash;

use crate::data_structures::HashMap;
use crate::visit::Flags;
use crate::{Interner, TypeFlags};

pub struct FoldCache<ST, R, const EXPAND_INFER: bool, I: Interner> {
    cache: HashMap<(I::Ty, ST), R>,
}

impl<ST, R, const EXPAND_INFER: bool, I: Interner> Default for FoldCache<ST, R, EXPAND_INFER, I> {
    fn default() -> Self {
        FoldCache { cache: Default::default() }
    }
}

impl<ST: Hash + Eq, R: Copy, const EXPAND_INFER: bool, I: Interner>
    FoldCache<ST, R, EXPAND_INFER, I>
{
    fn flags(&self) -> TypeFlags {
        let mut flags = TypeFlags::TYPE_COMPLEXITY_HIGH;
        if EXPAND_INFER {
            flags |= TypeFlags::HAS_INFER & !TypeFlags::HAS_RE_INFER;
        }
        flags
    }

    pub fn get(&mut self, ty: I::Ty, st: ST) -> Option<R> {
        if ty.flags().contains(self.flags()) { self.cache.get(&(ty, st)).copied() } else { None }
    }

    pub fn insert(&mut self, ty: I::Ty, st: ST, result: R) -> bool {
        if ty.flags().contains(self.flags()) {
            self.cache.insert((ty, st), result).is_none()
        } else {
            true
        }
    }
}
