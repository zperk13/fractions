macro_rules! macro_all_unsigned_primitive_ints {
    ($m:ident) => {
        $m! {u8}
        $m! {u16}
        $m! {u32}
        $m! {u64}
        $m! {u128}
        $m! {usize}
    };
}

pub(crate) use macro_all_unsigned_primitive_ints;
