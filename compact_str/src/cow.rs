use core::{
    borrow::{Borrow, BorrowMut},
    marker::PhantomData,
    str::Utf8Error,
};

use crate::{repr::Repr, CompactString, ReserveError, UnwrapWithMsg, Utf16Error};

#[repr(transparent)]
pub struct CompactCowStr<'a>(Repr, PhantomData<&'a ()>);

static_assertions::assert_eq_size!(CompactString, CompactCowStr);
static_assertions::assert_eq_align!(CompactString, CompactCowStr);

impl<'a> CompactCowStr<'a> {
    #[inline]
    const fn new_raw(repr: Repr) -> Self {
        CompactCowStr(repr, PhantomData)
    }

    /// Creates a new [`CompactString`] from any type that implements `AsRef<str>`.
    /// If the string is short enough, then it will be inlined on the stack!
    ///
    /// In a `static` or `const` context you can use the method [`CompactString::const_new()`].
    ///
    /// # Examples
    ///
    /// ### Inlined
    /// ```
    /// # use compact_str::CompactString;
    /// // We can inline strings up to 12 characters long on 32-bit architectures...
    /// #[cfg(target_pointer_width = "32")]
    /// let s = "i'm 12 chars";
    /// // ...and up to 24 characters on 64-bit architectures!
    /// #[cfg(target_pointer_width = "64")]
    /// let s = "i am 24 characters long!";
    ///
    /// let compact = CompactString::new(&s);
    ///
    /// assert_eq!(compact, s);
    /// // we are not allocated on the heap!
    /// assert!(!compact.is_heap_allocated());
    /// ```
    ///
    /// ### Heap
    /// ```
    /// # use compact_str::CompactString;
    /// // For longer strings though, we get allocated on the heap
    /// let long = "I am a longer string that will be allocated on the heap";
    /// let compact = CompactString::new(long);
    ///
    /// assert_eq!(compact, long);
    /// // we are allocated on the heap!
    /// assert!(compact.is_heap_allocated());
    /// ```
    ///
    /// ### Creation
    /// ```
    /// use compact_str::CompactString;
    ///
    /// // Using a `&'static str`
    /// let s = "hello world!";
    /// let hello = CompactString::new(&s);
    ///
    /// // Using a `String`
    /// let u = String::from("🦄🌈");
    /// let unicorn = CompactString::new(u);
    ///
    /// // Using a `Box<str>`
    /// let b: Box<str> = String::from("📦📦📦").into_boxed_str();
    /// let boxed = CompactString::new(&b);
    /// ```
    #[inline]
    #[track_caller]
    pub fn new<T: AsRef<str>>(text: T) -> Self {
        Self::new_raw(Repr::new_ref(text.as_ref()))
    }

    /// Get back the `&'static str` constructed by [`CompactString::const_new`].
    ///
    /// If the string was short enough that it could be inlined, then it was inline, and
    /// this method will return `None`.
    ///
    /// # Examples
    /// ```
    /// use compact_str::CompactString;
    ///
    /// const DEFAULT_NAME: CompactString =
    ///     CompactString::const_new("That is not dead which can eternal lie.");
    /// assert_eq!(
    ///     DEFAULT_NAME.as_static_str().unwrap(),
    ///     "That is not dead which can eternal lie.",
    /// );
    /// ```
    #[inline]
    #[rustversion::attr(since(1.64), const)]
    pub fn as_static_str(&self) -> Option<&'static str> {
        self.0.as_static_str()
    }

    /// Creates a new empty [`CompactString`] with the capacity to fit at least `capacity` bytes.
    ///
    /// A `CompactString` will inline strings on the stack, if they're small enough. Specifically,
    /// if the string has a length less than or equal to `std::mem::size_of::<String>` bytes
    /// then it will be inlined. This also means that `CompactString`s have a minimum capacity
    /// of `std::mem::size_of::<String>`.
    ///
    /// # Panics
    ///
    /// This method panics if the system is out-of-memory.
    /// Use [`CompactString::try_with_capacity()`] if you want to handle such a problem manually.
    ///
    /// # Examples
    ///
    /// ### "zero" Capacity
    /// ```
    /// # use compact_str::CompactString;
    /// // Creating a CompactString with a capacity of 0 will create
    /// // one with capacity of std::mem::size_of::<String>();
    /// let empty = CompactString::with_capacity(0);
    /// let min_size = std::mem::size_of::<String>();
    ///
    /// assert_eq!(empty.capacity(), min_size);
    /// assert_ne!(0, min_size);
    /// assert!(!empty.is_heap_allocated());
    /// ```
    ///
    /// ### Max Inline Size
    /// ```
    /// # use compact_str::CompactString;
    /// // Creating a CompactString with a capacity of std::mem::size_of::<String>()
    /// // will not heap allocate.
    /// let str_size = std::mem::size_of::<String>();
    /// let empty = CompactString::with_capacity(str_size);
    ///
    /// assert_eq!(empty.capacity(), str_size);
    /// assert!(!empty.is_heap_allocated());
    /// ```
    ///
    /// ### Heap Allocating
    /// ```
    /// # use compact_str::CompactString;
    /// // If you create a `CompactString` with a capacity greater than
    /// // `std::mem::size_of::<String>`, it will heap allocated. For heap
    /// // allocated strings we have a minimum capacity
    ///
    /// const MIN_HEAP_CAPACITY: usize = std::mem::size_of::<usize>() * 4;
    ///
    /// let heap_size = std::mem::size_of::<String>() + 1;
    /// let empty = CompactString::with_capacity(heap_size);
    ///
    /// assert_eq!(empty.capacity(), MIN_HEAP_CAPACITY);
    /// assert!(empty.is_heap_allocated());
    /// ```
    #[inline]
    #[track_caller]
    pub fn with_capacity(capacity: usize) -> Self {
        CompactString::with_capacity(capacity).into()
    }

    /// Fallible version of [`CompactString::with_capacity()`]
    ///
    /// This method won't panic if the system is out-of-memory, but return an [`ReserveError`].
    /// Otherwise it behaves the same as [`CompactString::with_capacity()`].
    #[inline]
    pub fn try_with_capacity(capacity: usize) -> Result<Self, ReserveError> {
        CompactString::try_with_capacity(capacity).map(Into::into)
    }

    /// Convert a slice of bytes into a [`CompactString`].
    ///
    /// A [`CompactString`] is a contiguous collection of bytes (`u8`s) that is valid [`UTF-8`](https://en.wikipedia.org/wiki/UTF-8).
    /// This method converts from an arbitrary contiguous collection of bytes into a
    /// [`CompactString`], failing if the provided bytes are not `UTF-8`.
    ///
    /// Note: If you want to create a [`CompactString`] from a non-contiguous collection of bytes,
    /// enable the `bytes` feature of this crate, and see `CompactString::from_utf8_buf`
    ///
    /// # Examples
    /// ### Valid UTF-8
    /// ```
    /// # use compact_str::CompactString;
    /// let bytes = vec![240, 159, 166, 128, 240, 159, 146, 175];
    /// let compact = CompactString::from_utf8(bytes).expect("valid UTF-8");
    ///
    /// assert_eq!(compact, "🦀💯");
    /// ```
    ///
    /// ### Invalid UTF-8
    /// ```
    /// # use compact_str::CompactString;
    /// let bytes = vec![255, 255, 255];
    /// let result = CompactString::from_utf8(bytes);
    ///
    /// assert!(result.is_err());
    /// ```
    #[inline]
    pub fn from_utf8<B: AsRef<[u8]>>(buf: B) -> Result<Self, Utf8Error> {
        Repr::from_utf8_ref(buf).map(CompactCowStr::new_raw)
    }

    /// Converts a vector of bytes to a [`CompactString`] without checking that the string contains
    /// valid UTF-8.
    ///
    /// See the safe version, [`CompactString::from_utf8`], for more details.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed to it are valid
    /// UTF-8. If this constraint is violated, it may cause memory unsafety issues with future users
    /// of the [`CompactString`], as the rest of the standard library assumes that
    /// [`CompactString`]s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use compact_str::CompactString;
    /// // some bytes, in a vector
    /// let sparkle_heart = vec![240, 159, 146, 150];
    ///
    /// let sparkle_heart = unsafe {
    ///     CompactString::from_utf8_unchecked(sparkle_heart)
    /// };
    ///
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    #[must_use]
    #[track_caller]
    pub unsafe fn from_utf8_unchecked<B: AsRef<[u8]>>(buf: B) -> Self {
        todo!();
    }

    /// Decode a [`UTF-16`](https://en.wikipedia.org/wiki/UTF-16) slice of bytes into a
    /// [`CompactString`], returning an [`Err`] if the slice contains any invalid data.
    ///
    /// # Examples
    /// ### Valid UTF-16
    /// ```
    /// # use compact_str::CompactString;
    /// let buf: &[u16] = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0x0069, 0x0063];
    /// let compact = CompactString::from_utf16(buf).unwrap();
    ///
    /// assert_eq!(compact, "𝄞music");
    /// ```
    ///
    /// ### Invalid UTF-16
    /// ```
    /// # use compact_str::CompactString;
    /// let buf: &[u16] = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0xD800, 0x0069, 0x0063];
    /// let res = CompactString::from_utf16(buf);
    ///
    /// assert!(res.is_err());
    /// ```
    #[inline]
    pub fn from_utf16<B: AsRef<[u16]>>(buf: B) -> Result<Self, Utf16Error> {
        CompactString::from_utf16(buf).map(Into::into)
    }

    /// Decode a UTF-16–encoded slice `v` into a `CompactString`, replacing invalid data with
    /// the replacement character (`U+FFFD`), �.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use compact_str::CompactString;
    /// // 𝄞mus<invalid>ic<invalid>
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075,
    ///           0x0073, 0xDD1E, 0x0069, 0x0063,
    ///           0xD834];
    ///
    /// assert_eq!(CompactString::from("𝄞mus\u{FFFD}ic\u{FFFD}"),
    ///            CompactString::from_utf16_lossy(v));
    /// ```
    #[inline]
    pub fn from_utf16_lossy<B: AsRef<[u16]>>(buf: B) -> Self {
        CompactString::from_utf16_lossy(buf).into()
    }

    /// Returns the length of the [`CompactString`] in `bytes`, not [`char`]s or graphemes.
    ///
    /// When using `UTF-8` encoding (which all strings in Rust do) a single character will be 1 to 4
    /// bytes long, therefore the return value of this method might not be what a human considers
    /// the length of the string.
    ///
    /// # Examples
    /// ```
    /// # use compact_str::CompactString;
    /// let ascii = CompactString::new("hello world");
    /// assert_eq!(ascii.len(), 11);
    ///
    /// let emoji = CompactString::new("👱");
    /// assert_eq!(emoji.len(), 4);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the [`CompactString`] has a length of 0, `false` otherwise
    ///
    /// # Examples
    /// ```
    /// # use compact_str::CompactString;
    /// let mut msg = CompactString::new("");
    /// assert!(msg.is_empty());
    ///
    /// // add some characters
    /// msg.push_str("hello reader!");
    /// assert!(!msg.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the capacity of the [`CompactString`], in bytes.
    ///
    /// # Note
    /// * A `CompactString` will always have a capacity of at least `std::mem::size_of::<String>()`
    ///
    /// # Examples
    /// ### Minimum Size
    /// ```
    /// # use compact_str::CompactString;
    /// let min_size = std::mem::size_of::<String>();
    /// let compact = CompactString::new("");
    ///
    /// assert!(compact.capacity() >= min_size);
    /// ```
    ///
    /// ### Heap Allocated
    /// ```
    /// # use compact_str::CompactString;
    /// let compact = CompactString::with_capacity(128);
    /// assert_eq!(compact.capacity(), 128);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Ensures that this [`CompactString`]'s capacity is at least `additional` bytes longer than
    /// its length. The capacity may be increased by more than `additional` bytes if it chooses,
    /// to prevent frequent reallocations.
    ///
    /// # Note
    /// * A `CompactString` will always have at least a capacity of `std::mem::size_of::<String>()`
    /// * Reserving additional bytes may cause the `CompactString` to become heap allocated
    ///
    /// # Panics
    /// This method panics if the new capacity overflows `usize` or if the system is out-of-memory.
    /// Use [`CompactString::try_reserve()`] if you want to handle such a problem manually.
    ///
    /// # Examples
    /// ```
    /// # use compact_str::CompactString;
    ///
    /// const WORD: usize = std::mem::size_of::<usize>();
    /// let mut compact = CompactString::default();
    /// assert!(compact.capacity() >= (WORD * 3) - 1);
    ///
    /// compact.reserve(200);
    /// assert!(compact.is_heap_allocated());
    /// assert!(compact.capacity() >= 200);
    /// ```
    #[inline]
    #[track_caller]
    pub fn reserve(&mut self, additional: usize) {
        self.try_reserve(additional).unwrap_with_msg()
    }

    /// Fallible version of [`CompactString::reserve()`]
    ///
    /// This method won't panic if the system is out-of-memory, but return an [`ReserveError`]
    /// Otherwise it behaves the same as [`CompactString::reserve()`].
    #[inline]
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), ReserveError> {
        self.0.reserve(additional)
    }

    /// Returns a string slice containing the entire [`CompactString`].
    ///
    /// # Examples
    /// ```
    /// # use compact_str::CompactString;
    /// let s = CompactString::new("hello");
    ///
    /// assert_eq!(s.as_str(), "hello");
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Returns a mutable string slice containing the entire [`CompactString`].
    ///
    /// # Examples
    /// ```
    /// # use compact_str::CompactString;
    /// let mut s = CompactString::new("hello");
    /// s.as_mut_str().make_ascii_uppercase();
    ///
    /// assert_eq!(s.as_str(), "HELLO");
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        let len = self.len();
        unsafe { core::str::from_utf8_unchecked_mut(&mut self.0.as_mut_buf()[..len]) }
    }
}

impl<'a> From<CompactString> for CompactCowStr<'a> {
    #[inline]
    fn from(value: CompactString) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

impl<'a> From<&'a CompactString> for CompactCowStr<'a> {
    #[inline]
    fn from(value: &'a CompactString) -> Self {
        if value.is_heap_allocated() {
            Self::new(value.as_str())
        } else {
            value.clone().into()
        }
    }
}

impl<'a> From<CompactCowStr<'a>> for CompactString {
    #[inline]
    fn from(mut value: CompactCowStr<'a>) -> Self {
        value.0.owned();
        unsafe { std::mem::transmute(value) }
    }
}

impl<'a> Borrow<str> for CompactCowStr<'a> {
    fn borrow(&self) -> &str {
        &self.as_str()
    }
}

impl<'a> BorrowMut<str> for CompactCowStr<'a> {
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}
