pub const NUMERIC: CharsLut = chars_lut(b"0123456789");
pub const NEWLINE: CharsLut = chars_lut(b"\n\r");
pub const INDENT: CharsLut = chars_lut(b" \t");

pub struct CharsLut([bool; 256]);
impl CharsLut {
    pub const fn contains(&self, needle: char) -> bool {
        self.0[needle as usize]
    }

    //pub const fn inner(&self) -> [bool; 256] {
    //    return self.0;
    //}
}

const fn chars_lut(chars: &[u8]) -> CharsLut {
    let mut res = [false; 256];

    let mut i = 0;
    while i < chars.len() {
        res[chars[i] as usize] = true;
        i += 1;
    }

    CharsLut(res)
}
