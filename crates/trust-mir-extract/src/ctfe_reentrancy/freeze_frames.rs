// Trust: a freeze guard removes only its own policy frame. Rust permits an
// outer guard to be explicitly dropped before an inner guard, so position in
// the vector is not ownership. Rc identity is private, non-reusable while
// live, and keeps both the token and the enclosing guard thread-bound.
use std::rc::Rc;

pub(super) struct FrameToken(Rc<()>);

pub(super) struct FreezeFrames<K> {
    frames: Vec<(Rc<()>, Option<K>)>,
}

impl<K> FreezeFrames<K> {
    pub(super) const fn new() -> Self {
        Self { frames: Vec::new() }
    }

    pub(super) fn enter(&mut self, body: Option<K>) -> FrameToken {
        let token = Rc::new(());
        self.frames.push((Rc::clone(&token), body));
        FrameToken(token)
    }

    pub(super) fn remove(&mut self, token: &FrameToken) -> bool {
        let Some(index) = self.frames.iter().position(|(owner, _)| Rc::ptr_eq(owner, &token.0)) else {
            return false;
        };
        self.frames.remove(index);
        true
    }

    pub(super) fn len(&self) -> usize {
        self.frames.len()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.frames.is_empty()
    }

    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = &Option<K>> {
        self.frames.iter().map(|(_, body)| body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn removing_outer_preserves_the_live_inner_body() {
        let mut frames = FreezeFrames::new();
        let outer = frames.enter(Some(10));
        let inner = frames.enter(Some(20));
        assert!(frames.remove(&outer));
        assert_eq!(frames.iter().copied().collect::<Vec<_>>(), vec![Some(20)]);
        assert!(!frames.is_empty());
        assert!(frames.remove(&inner));
        assert!(frames.is_empty());
    }

    #[test]
    fn removing_outer_preserves_an_unnamed_refusal_and_retired_tokens_cannot_remove_it() {
        let mut frames = FreezeFrames::new();
        let outer = frames.enter(Some(10));
        let inner = frames.enter(None);
        assert!(frames.remove(&outer));
        assert!(!frames.remove(&outer));
        assert_eq!(frames.iter().copied().collect::<Vec<_>>(), vec![None]);
        assert!(frames.remove(&inner));
        assert!(frames.is_empty());
    }

    #[test]
    fn distinct_nested_owners_with_identical_body_names_remain_distinct() {
        let mut frames = FreezeFrames::new();
        let outer = frames.enter(Some(10));
        let inner = frames.enter(Some(10));
        assert_eq!(frames.len(), 2);
        assert!(frames.remove(&outer));
        assert_eq!(frames.iter().copied().collect::<Vec<_>>(), vec![Some(10)]);
        assert!(!frames.remove(&outer));
        assert_eq!(frames.len(), 1);
        assert!(frames.remove(&inner));
        assert!(frames.is_empty());
    }
}
