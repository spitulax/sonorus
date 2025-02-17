pub const NUMERIC: CharsLUT = chars_lut(b"0123456789");
pub const NEWLINE: CharsLUT = chars_lut(b"\n\r");

pub struct CharsLUT([bool; 256]);
impl CharsLUT {
    pub const fn contains(&self, needle: char) -> bool {
        self.0[needle as usize]
    }

    //pub const fn inner(&self) -> [bool; 256] {
    //    return self.0;
    //}
}

const fn chars_lut(chars: &[u8]) -> CharsLUT {
    let mut res = [false; 256];

    let mut i = 0;
    while i < chars.len() {
        res[chars[i] as usize] = true;
        i += 1;
    }

    CharsLUT(res)
}
