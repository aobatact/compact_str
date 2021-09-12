use crate::repr::Repr;

#[derive(Clone)]
pub struct SmartStr {
    repr: Repr,
}

impl SmartStr {
    #[inline]
    pub fn new<T: AsRef<str>>(text: T) -> Self {
        SmartStr {
            repr: Repr::new(text),
        }
    }

    #[inline(always)]
    pub fn as_str(&self) -> &str {
        self.repr.as_str()
    }

    #[inline]
    pub fn is_heap_allocated(&self) -> bool {
        self.repr.is_heap_allocated()
    }
}

#[cfg(test)]
mod tests {
    use super::SmartStr;

    #[test]
    fn sanity_test() {
        let small_str = SmartStr::new("hello world");
        assert_eq!(small_str.as_str(), "hello world");

        let large_str = SmartStr::new("Lorem ipsum dolor sit amet");
        assert_eq!(large_str.as_str(), "Lorem ipsum dolor sit amet");
    }
}

#[cfg(test)]
mod randomized {
    use super::SmartStr;
    use proptest::prelude::*;

    #[cfg(target_pointer_width = "64")]
    const INLINED_SIZE: usize = 23;
    #[cfg(target_pointer_width = "32")]
    const INLINED_SIZE: usize = 11;

    proptest! {
        #[test]
        fn test_form_strings_correctly(word in "[.*]{0,1000}") {
            let smartstr = SmartStr::new(&word);

            // strings should be equal
            prop_assert_eq!(&word, smartstr.as_str());

            // strings with length INLINED_SIZE bytes or less should not be heap allocatated
            match word.len() {
                0..=INLINED_SIZE => prop_assert!(!smartstr.is_heap_allocated()),
                _ => prop_assert!(smartstr.is_heap_allocated()),
            }
        }
    }
}
