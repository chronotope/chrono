#![cfg_attr(docsrs, doc(cfg(feature = "arbitrary")))]

use super::NaiveTime;
use arbitrary::{Arbitrary, Unstructured};

impl Arbitrary<'_> for NaiveTime {
    fn arbitrary(u: &mut Unstructured) -> arbitrary::Result<NaiveTime> {
        let secs = u.int_in_range(0..=86_399)?;
        let nano = u.int_in_range(0..=1_999_999_999)?;
        let time = NaiveTime::from_num_seconds_from_midnight_opt(secs, nano)
            .expect("Could not generate a valid chrono::NaiveTime. It looks like implementation of Arbitrary for NaiveTime is erroneous.");
        Ok(time)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const UNSTRCUTURED_BINARY1: [u8; 8] = [0x8f, 0xc2, 0x95, 0xdc, 0x3e, 0x45, 0xb2, 0x3e];
    const UNSTRCUTURED_BINARY2: [u8; 8] = [0x8b, 0xad, 0x2c, 0xc9, 0xf0, 0x05, 0x75, 0x84];

    #[test]
    fn test_different_unstructured() {
        let mut unstrctured1 = Unstructured::new(&UNSTRCUTURED_BINARY1);
        let time1 = NaiveTime::arbitrary(&mut unstrctured1).unwrap();

        let mut unstrctured2 = Unstructured::new(&UNSTRCUTURED_BINARY2);
        let time2 = NaiveTime::arbitrary(&mut unstrctured2).unwrap();

        assert_ne!(time1, time2);
    }

    #[test]
    fn test_same_unstructured() {
        let mut unstrctured1 = Unstructured::new(&UNSTRCUTURED_BINARY1);
        let time1 = NaiveTime::arbitrary(&mut unstrctured1).unwrap();

        let mut unstrctured2 = Unstructured::new(&UNSTRCUTURED_BINARY1);
        let time2 = NaiveTime::arbitrary(&mut unstrctured2).unwrap();

        assert_eq!(time1, time2);
    }
}
