#[derive(Debug)]
pub enum JpgExtractError {
    Io(std::io::Error),
    FromBytes(img_parts::Error),
    MissingApp6,
    InvalidApp6,
}

impl std::error::Error for JpgExtractError {}

impl std::fmt::Display for JpgExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            JpgExtractError::Io(e) => e.fmt(f),
            JpgExtractError::FromBytes(e) => e.fmt(f),
            JpgExtractError::MissingApp6 => write!(f, "Missing APP6"),
            JpgExtractError::InvalidApp6 => write!(f, "Invalid APP6"),
        }
    }
}

impl From<img_parts::Error> for JpgExtractError {
    fn from(e: img_parts::Error) -> Self {
        JpgExtractError::FromBytes(e)
    }
}

impl From<std::io::Error> for JpgExtractError {
    fn from(e: std::io::Error) -> Self {
        JpgExtractError::Io(e)
    }
}
