//! Helpers to write the file.

use std::fs;
use std::io;
use std::io::Write;
use std::ops::{Add, AddAssign, Mul, Rem};

use byteorder::{BigEndian, LittleEndian, WriteBytesExt};

use crate::ifd::values::Offsets;

/// Trait for offset sizes (u32 for TIFF, u64 for BigTIFF).
///
/// This trait abstracts over the integer type used for file offsets,
/// allowing the same code to work with both standard TIFF (32-bit offsets)
/// and Big///*TIFF (64-bit offsets).
pub trait OffsetSize:
    Copy
    + Default
    + Add<Output = Self>
    + AddAssign
    + Mul<Output = Self>
    + Rem<Output = Self>
    + PartialOrd
    + PartialEq
    + std::fmt::Debug
    + 'static
{
    /// The inline value threshold (4 for TIFF, 8 for BigTIFF).
    const INLINE_THRESHOLD: Self;

    /// Zero value.
    const ZERO: Self;

    /// One value.
    const ONE: Self;

    /// Two value (for word boundary checks).
    const TWO: Self;

    /// Checked addition that returns None on overflow.
    fn checked_add(self, rhs: Self) -> Option<Self>;

    /// Write this offset value to an EndianFile.
    fn write_to(self, file: &mut EndianFile) -> io::Result<()>;

    /// Convert from usize (for lengths).
    fn from_usize(val: usize) -> Self;

    /// Convert to u64 for comparisons and calculations.
    fn to_u64(self) -> u64;
}

impl OffsetSize for u32 {
    const INLINE_THRESHOLD: Self = 4;
    const ZERO: Self = 0;
    const ONE: Self = 1;
    const TWO: Self = 2;

    fn checked_add(self, rhs: Self) -> Option<Self> {
        u32::checked_add(self, rhs)
    }

    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        file.write_u32(self)
    }

    fn from_usize(val: usize) -> Self {
        val as u32
    }

    fn to_u64(self) -> u64 {
        self as u64
    }
}

impl OffsetSize for u64 {
    const INLINE_THRESHOLD: Self = 8;
    const ZERO: Self = 0;
    const ONE: Self = 1;
    const TWO: Self = 2;

    fn checked_add(self, rhs: Self) -> Option<Self> {
        u64::checked_add(self, rhs)
    }

    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        file.write_u64(self)
    }

    fn from_usize(val: usize) -> Self {
        val as u64
    }

    fn to_u64(self) -> u64 {
        self
    }
}

/// The byte order used within the TIFF file.
///
/// There are two possible values: II (little-endian or Intel format)
/// and MM (big-endian or Motorola format).
#[derive(Clone, Copy)]
pub enum Endianness {
    /// Intel byte order, also known as little-endian.
    ///
    /// The byte order is always from the least significant byte to
    /// the most significant byte.
    II,

    /// Motorola byte order, also known as big-endian.
    ///
    /// The byte order is always from the most significant byte to
    /// the least significant byte.
    MM,
}

impl Endianness {
    /// Returns the u16 value that represents the given endianness
    /// in a Tagged Image File Header.
    pub(crate) fn id(&self) -> u16 {
        match &self {
            Endianness::II => 0x4949,
            Endianness::MM => 0x4d4d,
        }
    }
}

/// Used during the allocation phase of the process of creating
/// a TIFF file.
///
/// Holds the number of bytes that were allocated, in order to
/// calculate the needed offsets.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
#[doc(hidden)]
pub struct Cursor<O: OffsetSize>(O);

impl<O: OffsetSize> Cursor<O> {
    /// Creates a new `Cursor` with no bytes allocated.
    pub(crate) fn new() -> Self {
        Cursor(O::ZERO)
    }

    /// Allocates a number of bytes to the `Cursor`.
    ///
    /// # Panics
    ///
    /// Attempting to allocate more space than the offset type allows will `panic`.
    pub(crate) fn allocate(&mut self, n: O) {
        self.0 = match self.0.checked_add(n) {
            Some(val) => val,
            None => panic!("Attempted to write a TIFF file bigger than the offset type allows."),
        };
    }

    /// Returns the number of already allocated bytes.
    pub(crate) fn allocated_bytes(&self) -> O {
        self.0
    }
}

/// Type alias for standard TIFF cursor (32-bit offsets).
pub type TiffCursor = Cursor<u32>;

/// Type alias for BigTIFF cursor (64-bit offsets).
pub type BigTiffCursor = Cursor<u64>;

/// Helper structure that provides convenience methods to write to
/// a `fs::File`, being aware of the file's [`Endianness`].
///
/// [`Endianness`]: enum.Endianness.html
pub struct EndianFile {
    file: fs::File,
    byte_order: Endianness,
    written_bytes: u64,
}

impl Into<fs::File> for EndianFile {
    fn into(self) -> fs::File {
        self.file
    }
}

impl EndianFile {
    /// Gets the number of written bytes to this file.
    pub(crate) fn new(file: fs::File, byte_order: Endianness) -> Self {
        Self {
            file,
            byte_order,
            written_bytes: 0,
        }
    }

    /// Gets the number of written bytes to this file.
    pub(crate) fn written_bytes(&self) -> u64 {
        self.written_bytes
    }
}

impl EndianFile {
    /// Writes a u8 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u8(&mut self, n: u8) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_u8(n)
    }

    /// Writes a slice of bytes to a file.
    ///
    /// This is much more efficient than calling [`write_u8`] in a loop if you have list
    /// of bytes to write.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_all_u8(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.written_bytes += bytes.len() as u64;
        self.file.write_all(bytes)
    }

    /// Writes a u16 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u16(&mut self, n: u16) -> io::Result<()> {
        self.written_bytes += 2 as u64;
        match self.byte_order {
            Endianness::II => {
                self.file.write_u16::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_u16::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    pub fn write_u32(&mut self, n: u32) -> io::Result<()> {
        self.written_bytes += 4;
        match self.byte_order {
            Endianness::II => {
                self.file.write_u32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_u32::<BigEndian>(n)?;
            }
        }

        Ok(())
    }

    /// Writes a u64 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_u64(&mut self, n: u64) -> io::Result<()> {
        self.written_bytes += 8;
        match self.byte_order {
            Endianness::II => {
                self.file.write_u64::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_u64::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a i8 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i8(&mut self, n: i8) -> io::Result<()> {
        self.written_bytes += 1 as u64;
        self.file.write_i8(n)
    }

    /// Writes a i16 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i16(&mut self, n: i16) -> io::Result<()> {
        self.written_bytes += 2 as u64;
        match self.byte_order {
            Endianness::II => {
                self.file.write_i16::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_i16::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a i32 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_i32(&mut self, n: i32) -> io::Result<()> {
        self.written_bytes += 4 as u64;
        match self.byte_order {
            Endianness::II => {
                self.file.write_i32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_i32::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a f32 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_f32(&mut self, n: f32) -> io::Result<()> {
        self.written_bytes += 4 as u64;
        match self.byte_order {
            Endianness::II => {
                self.file.write_f32::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_f32::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes a f64 to the file.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    pub fn write_f64(&mut self, n: f64) -> io::Result<()> {
        self.written_bytes += 8;
        match self.byte_order {
            Endianness::II => {
                self.file.write_f64::<LittleEndian>(n)?;
            }
            Endianness::MM => {
                self.file.write_f64::<BigEndian>(n)?;
            }
        }
        Ok(())
    }

    /// Writes an arbitraty byte to the file.
    ///
    /// This is useful when there is need to write an extra byte
    /// to guarantee that all offsets are even but that byte
    /// doesn't really hold any information.
    pub(crate) fn write_arbitrary_byte(&mut self) -> io::Result<()> {
        self.written_bytes += 1;
        self.file.write_u8(0)
    }
}

/// A block of data in the file pointed to by a field value, but
/// that isn't part of the field itself (such as image strips).
///
/// It is also possible to store any block of data in a [`ByteBlock`],
/// but that would require to know the [`Endianness`] of the file
/// beforehand, so the bytes are written in the correct order.
///
/// Using a `Datablock`, on the other hand, allows to make use
/// of the functionality of an [`EndianFile`], so the data can be
/// written without worrying about the endianness.
///
/// # Examples
///
/// Creating a DataBlock for `Vec<u32>`:
/// ```
/// use std::io;
/// use tiff_encoder::write::{Datablock, EndianFile};
/// use tiff_encoder::ifd::values::Offsets;
///
/// // Create a block that wraps the u32 data.
/// struct U32Block(Vec<u32>);
/// // Implement datablock functions
/// impl Datablock for U32Block {
///     fn size(&self) -> u64 {
///         // Each u32 occupies 4 bytes.
///         self.0.len() as u64 * 4
///     }
///     fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
///         for val in self.0 {
///             file.write_u32(val)?
///         }
///         Ok(())
///     }
/// }
/// // (Optional) implement some convenient functions to construct Offsets
/// impl U32Block {
///     // Construct an Offsets to multiple U32Block
///     pub fn offsets(blocks: Vec<Vec<u32>>) -> Offsets<Self> {
///         Offsets::new(blocks.into_iter().map(|block| U32Block(block)).collect())
///     }
///     // Construct an Offsets to a single U32Block
///     pub fn single(block: Vec<u32>) -> Offsets<Self> {
///         U32Block::offsets(vec![block])
///     }
/// }
///
/// // A vector holding arbitrary u32 data.
/// // This is the data we want to store in the U32Block.
/// let data_32bits: Vec<u32> = vec![0; 65536];
///
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = U32Block::single(data_32bits);
/// ```
///
/// [`ByteBlock`]: struct.ByteBlock.html
/// [`Endianness`]: enum.Endianness.html
/// [`EndianFile`]: struct.EndianFile.html
pub trait Datablock {
    /// The number of bytes occupied by this `Datablock`.
    ///
    /// # Panics
    ///
    /// The number of written bytes to the [`EndianFile`] in
    /// [`write_to(self, &mut EndianFile)`] must be the same value returned
    /// by this function.
    ///
    /// Failing to meet that specification will `panic`.
    ///
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`write_to(self, &mut EndianFile)`]: #method.write_to
    fn size(&self) -> u64;

    /// Writes this `Datablock` to an [`EndianFile`]. The number of bytes
    /// written must be exactly same number as returned by [`size(&self)`].
    ///
    /// # Panics
    ///
    /// Failing to write the exact same number of bytes as indicated in
    /// [`size(&self)`] will `panic`.
    ///
    /// [`EndianFile`]: struct.EndianFile.html
    /// [`size(&self)`]: #method.size
    fn write_to(self, file: &mut EndianFile) -> io::Result<()>;
}

/// [`Datablock`] that consists of a list of bytes.
///
/// It is possible to store any block of data in a `ByteBlock`,
/// but that would require to know the [`Endianness`] of the file
/// beforehand, so the bytes are written in the correct order.
///
/// Using a [`Datablock`], on the other hand, allows to make use
/// of the functionality of an [`EndianFile`], so the data can be
/// written without worrying about the endianness.
///
/// # Examples
///
/// Creating a ByteBlock from a `Vec<u8>`:
/// ```
/// use tiff_encoder::prelude::*;
///
/// // A vector holding arbitrary u8 data.
/// // This is the data we want to store as a Byteblock.
/// let data_8bits: Vec<u8> = vec![0; 65536];
///
/// // Create an Offsets of a single Byteblock from the buffer.
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = ByteBlock::single(data_8bits);
/// ```
///
/// Creating a ByteBlock from a `Vec<u32>`:
/// ```
/// extern crate byteorder;
/// // Crate byteorder will be used to write 32-bit information in a 8-bit buffer.
/// use byteorder::{LittleEndian, WriteBytesExt};
/// use tiff_encoder::prelude::*;
///
///
/// // A vector holding arbitrary u32 data.
/// // This is the data we want to store as a Byteblock.
/// let data_32bits: Vec<u32> = vec![0; 65536];
///
/// // First, let's store the data in a u8 buffer.
/// let mut image_bytes = Vec::with_capacity(262144); // 65536*4 (each u32 has a size of 4 bytes)
/// for val in data_32bits {
///     // A little endian TIFF file is assumed in this example.
///     image_bytes.write_u32::<LittleEndian>(val).unwrap();
/// }
///
/// // Create an Offsets of a single Byteblock from the buffer.
/// // This is the value that can be used directly as an IFD entry value.
/// let byte_block = ByteBlock::single(image_bytes);
/// ```
///
///
/// [`Datablock`]: trait.Datablock.html
/// [`EndianFile`]: struct.EndianFile.html
/// [`Endianness`]: enum.Endianness.html
pub struct ByteBlock(pub Vec<u8>);
impl ByteBlock {
    /// Constructs an [`Offsets`] of `ByteBlock`s from a vector of
    /// vectors of bytes.
    ///
    /// Each vector of bytes represents one `ByteBlock`.
    ///
    /// [`Offsets`]: ifd/values/struct.Offsets.html
    pub fn offsets(blocks: Vec<Vec<u8>>) -> Offsets<ByteBlock> {
        Offsets::new(blocks.into_iter().map(|block| ByteBlock(block)).collect())
    }

    /// Constructs an [`Offsets`] from a vector of bytes.
    ///
    /// This vector of bytes represents a single `ByteBlock`.
    ///
    /// [`Offsets`]: ifd/values/struct.Offsets.html
    pub fn single(block: Vec<u8>) -> Offsets<ByteBlock> {
        ByteBlock::offsets(vec![block])
    }

    /// Constructs a BigTIFF-compatible [`Offsets`] of `ByteBlock`s from a vector of
    /// vectors of bytes.
    ///
    /// Each vector of bytes represents one `ByteBlock`.
    ///
    /// [`Offsets`]: ifd/values/struct.Offsets.html
    pub fn big_offsets(blocks: Vec<Vec<u8>>) -> Offsets<ByteBlock, u64> {
        Offsets::new(blocks.into_iter().map(|block| ByteBlock(block)).collect())
    }

    /// Constructs a BigTIFF-compatible [`Offsets`] from a vector of bytes.
    ///
    /// This vector of bytes represents a single `ByteBlock`.
    ///
    /// [`Offsets`]: ifd/values/struct.Offsets.html
    pub fn big_single(block: Vec<u8>) -> Offsets<ByteBlock, u64> {
        ByteBlock::big_offsets(vec![block])
    }
}
impl Datablock for ByteBlock {
    fn size(&self) -> u64 {
        self.0.len() as u64
    }

    fn write_to(self, file: &mut EndianFile) -> io::Result<()> {
        file.write_all_u8(&self.0)?;
        Ok(())
    }
}
