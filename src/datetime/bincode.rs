use crate::DateTime;
use crate::TimeZone;
use crate::Utc;
use bincode::BorrowDecode;
use bincode::Decode;
use bincode::Encode;
use bincode::de::BorrowDecoder;
use bincode::de::Decoder;
use bincode::enc::Encoder;
use bincode::error::DecodeError;
use bincode::error::EncodeError;

impl<Tz: TimeZone> Encode for DateTime<Tz> {
    fn encode<E: Encoder>(&self, encoder: &mut E) -> Result<(), EncodeError> {
        i64::encode(&self.timestamp(), encoder)?;
        u32::encode(&self.timestamp_subsec_nanos(), encoder)?;

        Ok(())
    }
}

impl<Context> Decode<Context> for DateTime<Utc> {
    fn decode<D: Decoder<Context = Context>>(decoder: &mut D) -> Result<Self, DecodeError> {
        let secs = i64::decode(decoder)?;
        let nsecs = u32::decode(decoder)?;

        Ok(DateTime::from_timestamp(secs, nsecs)
            .ok_or_else(|| DecodeError::Other("Could not decode UTC DateTime"))?)
    }
}
impl<'de, Context> BorrowDecode<'de, Context> for DateTime<Utc> {
    fn borrow_decode<D: BorrowDecoder<'de, Context = Context>>(
        decoder: &mut D,
    ) -> Result<Self, DecodeError> {
        let secs = i64::borrow_decode(decoder)?;
        let nsecs = u32::borrow_decode(decoder)?;

        Ok(DateTime::from_timestamp(secs, nsecs)
            .ok_or_else(|| DecodeError::Other("Could not decode UTC DateTime"))?)
    }
}

#[cfg(test)]
mod tests {
    use crate::DateTime;
    use crate::Utc;
    use bincode::config;

    #[test]
    fn bincode_utc_date_time() {
        let dt = Utc::now();

        let bytes = bincode::encode_to_vec(&dt, config::standard())
            .expect("Should have been able to encode UTC DateTime.");
        let (dt_decoded, _) =
            bincode::decode_from_slice::<DateTime<Utc>, _>(&bytes, config::standard())
                .expect("Should have been able to encode UTC DateTime.");

        assert_eq!(dt, dt_decoded);
    }
}
