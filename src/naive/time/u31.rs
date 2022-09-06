use core::{cmp, fmt, hash, mem};

/// A 31-bit unsigned integer
#[cfg(target_endian = "little")]
#[allow(unreachable_pub)] // public through `rkyv::Archive<NaiveTime>`
#[repr(C)]
#[derive(Copy, Clone)]
pub struct U31 {
    align: [u32; 0],
    a: u8,
    b: u8,
    c: u8,
    d: MaxByte,
}

/// A 31-bit unsigned integer
#[cfg(target_endian = "big")]
#[allow(unreachable_pub)] // public through `rkyv::Archive<NaiveTime>`
#[repr(C)]
#[derive(Copy, Clone)]
pub(crate) struct U31 {
    align: [u32; 0],
    d: MaxByte,
    c: u8,
    b: u8,
    a: u8,
}

impl U31 {
    pub(crate) const ZERO: U31 = U31 { align: [], a: 0, b: 0, c: 0, d: MaxByte::V0 };

    pub(crate) const SEC_MINUS_1: Self = {
        // [int(x, 16) for x in reversed(re.findall('..', f'{999_999_999:x}'))]
        U31 { align: [], a: 255, b: 201, c: 154, d: MaxByte::V59 }
    };

    /// SAFETY: the caller has to ensure that the value is in range
    #[inline]
    pub(crate) unsafe fn new_unchecked(value: u32) -> Self {
        mem::transmute(value)
    }

    #[inline]
    pub(crate) fn get(self) -> u32 {
        unsafe { mem::transmute(self) }
    }
}

impl fmt::Debug for U31 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.get().fmt(f)
    }
}

impl fmt::Display for U31 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.get().fmt(f)
    }
}

impl cmp::PartialEq for U31 {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl cmp::PartialOrd for U31 {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        self.get().partial_cmp(&other.get())
    }
}

impl cmp::Eq for U31 {}

impl cmp::Ord for U31 {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.get().cmp(&other.get())
    }
}

impl hash::Hash for U31 {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

impl Default for U31 {
    #[inline]
    fn default() -> Self {
        Self::ZERO
    }
}

#[allow(dead_code)]
#[repr(u8)]
#[derive(Copy, Clone)]
pub(crate) enum MaxByte {
    V0 = 0,
    V1 = 1,
    V2 = 2,
    V3 = 3,
    V4 = 4,
    V5 = 5,
    V6 = 6,
    V7 = 7,
    V8 = 8,
    V9 = 9,
    V10 = 10,
    V11 = 11,
    V12 = 12,
    V13 = 13,
    V14 = 14,
    V15 = 15,
    V16 = 16,
    V17 = 17,
    V18 = 18,
    V19 = 19,
    V20 = 20,
    V21 = 21,
    V22 = 22,
    V23 = 23,
    V24 = 24,
    V25 = 25,
    V26 = 26,
    V27 = 27,
    V28 = 28,
    V29 = 29,
    V30 = 30,
    V31 = 31,
    V32 = 32,
    V33 = 33,
    V34 = 34,
    V35 = 35,
    V36 = 36,
    V37 = 37,
    V38 = 38,
    V39 = 39,
    V40 = 40,
    V41 = 41,
    V42 = 42,
    V43 = 43,
    V44 = 44,
    V45 = 45,
    V46 = 46,
    V47 = 47,
    V48 = 48,
    V49 = 49,
    V50 = 50,
    V51 = 51,
    V52 = 52,
    V53 = 53,
    V54 = 54,
    V55 = 55,
    V56 = 56,
    V57 = 57,
    V58 = 58,
    V59 = 59,
    V60 = 60,
    V61 = 61,
    V62 = 62,
    V63 = 63,
    V64 = 64,
    V65 = 65,
    V66 = 66,
    V67 = 67,
    V68 = 68,
    V69 = 69,
    V70 = 70,
    V71 = 71,
    V72 = 72,
    V73 = 73,
    V74 = 74,
    V75 = 75,
    V76 = 76,
    V77 = 77,
    V78 = 78,
    V79 = 79,
    V80 = 80,
    V81 = 81,
    V82 = 82,
    V83 = 83,
    V84 = 84,
    V85 = 85,
    V86 = 86,
    V87 = 87,
    V88 = 88,
    V89 = 89,
    V90 = 90,
    V91 = 91,
    V92 = 92,
    V93 = 93,
    V94 = 94,
    V95 = 95,
    V96 = 96,
    V97 = 97,
    V98 = 98,
    V99 = 99,
    V100 = 100,
    V101 = 101,
    V102 = 102,
    V103 = 103,
    V104 = 104,
    V105 = 105,
    V106 = 106,
    V107 = 107,
    V108 = 108,
    V109 = 109,
    V110 = 110,
    V111 = 111,
    V112 = 112,
    V113 = 113,
    V114 = 114,
    V115 = 115,
    V116 = 116,
    V117 = 117,
    V118 = 118,
    V119 = 119,
    V120 = 120,
    V121 = 121,
    V122 = 122,
    V123 = 123,
    V124 = 124,
    V125 = 125,
    V126 = 126,
    V127 = 127,
}

#[cfg(feature = "rkyv")]
const _: () = {
    use rkyv::{Archive, Archived, Deserialize, Fallible, Resolver, Serialize};

    #[allow(missing_debug_implementations)] // we cannot know if `Archived<u32>` implements `Debug`
    #[allow(unreachable_pub)]
    pub struct ArchivedU31(Archived<u32>);

    #[allow(missing_debug_implementations)] // we cannot know if `Resolver<u32>` implements `Debug`
    #[allow(unreachable_pub)]
    pub struct U31Resolver(Resolver<u32>);

    impl Archive for U31 {
        type Archived = ArchivedU31;

        type Resolver = U31Resolver;

        #[inline]
        unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
            let nanos: &u32 = mem::transmute(&self);
            Archive::resolve(nanos, pos, resolver.0, out.cast());
        }
    }

    impl<D: Fallible + ?Sized> Deserialize<U31, D> for Archived<U31> {
        #[inline]
        fn deserialize(&self, deserializer: &mut D) -> Result<U31, <D as Fallible>::Error> {
            let nanos = Deserialize::<u32, D>::deserialize(&self.0, deserializer)?;
            Ok(unsafe { U31::new_unchecked(nanos) })
        }
    }

    impl<S: Fallible + ?Sized> Serialize<S> for U31 {
        #[inline]
        fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, <S as Fallible>::Error> {
            let nanos: &u32 = unsafe { mem::transmute(&self) };
            let nanos = Serialize::<S>::serialize(nanos, serializer)?;
            Ok(U31Resolver(nanos))
        }
    }
};
