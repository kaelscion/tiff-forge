//! The values contained or pointed at by an IFD Field.
//!
//! There are three groups of [`FieldValues`]: [`TiffTypeValues`],
//! [`Offsets`] and [`OffsetsToIfds`]. The first represents a list
//! of values of any given [`TiffType`]. The second represents a
//! list of [`LONG`] values, each pointing to a specific [`Datablock`].
//! The third represents a list of [`IFD`] values, each pointing to
//! an [`Ifd`].
//!
//! [`FieldValues`]: trait.FieldValues.html
//! [`TiffTypeValues`]: struct.TiffTypeValues.html
//! [`Offsets`]: struct.Offsets.html
//! [`OffsetsToIfds`]: struct.OffsetsToIfds.html
//! [`TiffType`]: ../types/trait.TiffType.html
//! [`LONG`]: ../types/struct.LONG.html
//! [`IFD`]: ../types/struct.IFD.html
//! [`Datablock`]: ../../write/trait.Datablock.html

use std::io;
use std::marker::PhantomData;

use crate::ifd::types::{BIGIFD, IFD, LONG, LONG8, TiffType};
use crate::ifd::{AllocatedIfdChain, IfdChain};
use crate::write::{Cursor, Datablock, EndianFile, OffsetSize};

/// The values contained or pointed at by an IFD Field.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// There are three groups of `FieldValues`: [`TiffTypeValues`],
/// [`Offsets`] and [`OffsetsToIfds`]. The first represents a list
/// of values of any given [`TiffType`]. The second represents a
/// list of [`LONG`] values, each pointing to a specific [`Datablock`].
/// The third represents a list of [`IFD`] values, each pointing to
/// an [`Ifd`].
///
/// This trait is sealed. It is not possible to implement it outside
/// this crate.
///
/// [`TiffTypeValues`]: struct.TiffTypeValues.html
/// [`Offsets`]: struct.Offsets.html
/// [`OffsetsToIfds`]: struct.OffsetsToIfds.html
/// [`TiffType`]: ../types/trait.TiffType.html
/// [`LONG`]: ../types/struct.LONG.html
/// [`IFD`]: ../types/struct.IFD.html
/// [`Datablock`]: ../../write/trait.Datablock.html
pub trait FieldValues<O: OffsetSize = u32>: private::Sealed<O> {
    /// The number of values the field contains.
    #[doc(hidden)]
    fn count(&self) -> O;
    /// The sum of the size of every value in this field.
    ///
    /// This doesn't include `Datablocks` owned by this field.
    #[doc(hidden)]
    fn size(&self) -> O;
    /// Allocates the needed space in the given `Cursor`, transforming into
    /// an `AllocatedFieldValues`.
    #[doc(hidden)]
    fn allocate(self: Box<Self>, c: &mut Cursor<O>) -> Box<dyn AllocatedFieldValues<O>>;
}

/// Allocated form of `FieldValues`
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
#[doc(hidden)]
pub trait AllocatedFieldValues<O: OffsetSize = u32> {
    /// The number of values the field contains.
    fn count(&self) -> O;
    /// The sum of the size of every value in this field.
    ///
    /// This doesn't include `Datablocks` owned by this field.
    fn size(&self) -> O;
    /// The offset to the first value (counting from the beginning of the file)
    /// if the values don't fit in the IFD entry (in other words, if `size()` is
    /// bigger than the inline threshold).
    fn position(&self) -> Option<O>;
    /// The TIFF 16-bit code that identifies the type of the values of the field.
    fn type_id(&self) -> u16;
    /// Write the values to the given `EndianFile`, as well as any other data
    /// they point to.
    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()>;
}

/// Seals FieldValues, so that it can only be implemented inside
/// the crate. There are only three types of FieldValues:
/// `Offsets` to datablocks, `OffsetsToIfds` and `TiffTypeValues`.
mod private {
    use crate::write::OffsetSize;

    pub trait Sealed<O: OffsetSize> {}
    impl<T: super::Datablock, O: OffsetSize> Sealed<O> for super::Offsets<T, O> {}
    impl<T, O: OffsetSize> Sealed<O> for super::TiffTypeValues<T, O> {}
    impl<O: OffsetSize> Sealed<O> for super::OffsetsToIfds<O> {}
}

/// A list of [`LONG`] values, each pointing to a specific
/// [`Datablock`].
///
/// This structure owns the list of Datablocks instead, so the user
/// doesn't have to deal with the offsets in the file. It is responsible
/// for writing both the offsets and the blocks of data.
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// [`LONG`]: ../types/struct.LONG.html
/// [`Datablock`]: ../../write/trait.Datablock.html
pub struct Offsets<T: Datablock, O: OffsetSize = u32> {
    pub data: Vec<T>,
    _phantom: PhantomData<O>,
}

impl<T: Datablock + 'static, O: OffsetSize> Offsets<T, O> {
    /// Creates a new `Offsets` instance from a vector of [`Datablock`]s.
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
    pub fn new(datablocks: Vec<T>) -> Self {
        Offsets {
            data: datablocks,
            _phantom: PhantomData,
        }
    }

    /// Creates a new `Offsets` instance from a single [`Datablock`].
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
    pub fn single(datablock: T) -> Self {
        Offsets::new(vec![datablock])
    }
}

impl<T: Datablock + 'static> Offsets<T, u32> {
    /// Creates a BigTIFF-compatible `Offsets` instance from a vector of [`Datablock`]s.
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
    pub fn big_new(datablocks: Vec<T>) -> Offsets<T, u64> {
        Offsets {
            data: datablocks,
            _phantom: PhantomData,
        }
    }

    /// Creates a BigTIFF-compatible `Offsets` instance from a single [`Datablock`].
    ///
    /// [`Datablock`]: ../../write/trait.Datablock.html
    pub fn big_single(datablock: T) -> Offsets<T, u64> {
        Offsets::big_new(vec![datablock])
    }
}

impl<T: Datablock + 'static> FieldValues<u32> for Offsets<T, u32> {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        <LONG as TiffType<u32>>::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor<u32>) -> Box<dyn AllocatedFieldValues<u32>> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            let offsets = Vec::new();
            let block_size = self.data.get(0).unwrap().size() as u32;

            c.allocate(if block_size % 2 == 0 {
                block_size
            } else {
                block_size + 1
            });

            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: self.data,
                _phantom: PhantomData,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());

            for block in self.data.iter() {
                offsets.push(LONG(c.allocated_bytes()));
                let block_size = block.size() as u32;
                c.allocate(if block_size % 2 == 0 {
                    block_size
                } else {
                    block_size + 1
                });
            }

            Box::new(AllocatedOffsets {
                position,
                offsets,
                data: self.data,
                _phantom: PhantomData,
            })
        }
    }
}

impl<T: Datablock + 'static> FieldValues<u64> for Offsets<T, u64> {
    fn count(&self) -> u64 {
        self.data.len() as u64
    }

    fn size(&self) -> u64 {
        <LONG8 as TiffType<u64>>::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor<u64>) -> Box<dyn AllocatedFieldValues<u64>> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            let offsets = Vec::new();
            let block_size = self.data.get(0).unwrap().size() as u64;

            c.allocate(if block_size % 2 == 0 {
                block_size
            } else {
                block_size + 1
            });

            Box::new(AllocatedOffsets64 {
                position,
                offsets,
                data: self.data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());

            for block in self.data.iter() {
                offsets.push(LONG8(c.allocated_bytes()));
                let block_size = block.size() as u64;
                c.allocate(if block_size % 2 == 0 {
                    block_size
                } else {
                    block_size + 1
                });
            }

            Box::new(AllocatedOffsets64 {
                position,
                offsets,
                data: self.data,
            })
        }
    }
}

/// Allocated form of `Offsets` for u32
struct AllocatedOffsets<T: Datablock, O: OffsetSize> {
    position: Option<O>,
    offsets: Vec<LONG>,
    data: Vec<T>,
    _phantom: PhantomData<O>,
}

impl<T: Datablock> AllocatedFieldValues<u32> for AllocatedOffsets<T, u32> {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        <LONG as TiffType<u32>>::size() * self.count()
    }

    fn position(&self) -> Option<u32> {
        self.position
    }

    fn type_id(&self) -> u16 {
        <LONG as TiffType<u32>>::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let AllocatedOffsets { data, offsets, .. } = unboxed;
        for offset in offsets {
            <LONG as TiffType<u32>>::write_to(offset, file)?;
        }
        for block in data {
            let file_initial = file.written_bytes();
            let block_size = block.size() as u64;
            block.write_to(file)?;
            let written_size = file.written_bytes() - file_initial;
            if written_size % 2 == 1 {
                file.write_arbitrary_byte()?
            }
            if written_size != block_size {
                panic!(
                    "The number of bytes allocated by the Datablock ({}) is different from the number of bytes written to the file ({}).",
                    block_size, written_size
                )
            }
        }
        Ok(())
    }
}

/// Allocated form of `Offsets` for u64
struct AllocatedOffsets64<T: Datablock> {
    position: Option<u64>,
    offsets: Vec<LONG8>,
    data: Vec<T>,
}

impl<T: Datablock> AllocatedFieldValues<u64> for AllocatedOffsets64<T> {
    fn count(&self) -> u64 {
        self.data.len() as u64
    }

    fn size(&self) -> u64 {
        <LONG8 as TiffType<u64>>::size() * self.count()
    }

    fn position(&self) -> Option<u64> {
        self.position
    }

    fn type_id(&self) -> u16 {
        <LONG8 as TiffType<u64>>::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let AllocatedOffsets64 { data, offsets, .. } = unboxed;
        for offset in offsets {
            <LONG8 as TiffType<u64>>::write_to(offset, file)?;
        }
        for block in data {
            let file_initial = file.written_bytes();
            let block_size = block.size() as u64;
            block.write_to(file)?;
            let written_size = file.written_bytes() - file_initial;
            if written_size % 2 == 1 {
                file.write_arbitrary_byte()?
            }
            if written_size != block_size {
                panic!(
                    "The number of bytes allocated by the Datablock ({}) is different from the number of bytes written to the file ({}).",
                    block_size, written_size
                )
            }
        }
        Ok(())
    }
}

/// A list of values of any given [`TiffType`].
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// [`TiffType`]: ../types/trait.TiffType.html
#[derive(Debug, PartialEq)]
pub struct TiffTypeValues<T, O: OffsetSize = u32> {
    values: Vec<T>,
    _phantom: PhantomData<O>,
}

impl<T, O: OffsetSize> TiffTypeValues<T, O> {
    /// Creates a new instance of `TiffTypeValues` from a vector
    /// of instances of any given [`TiffType`].
    ///
    /// [`TiffType`]: ../types/trait.TiffType.html
    pub fn new(values: Vec<T>) -> Self {
        if values.is_empty() {
            panic!("Cannot create an empty instance of TiffTypeValues")
        }
        TiffTypeValues {
            values,
            _phantom: PhantomData,
        }
    }
}

impl<T: TiffType<O> + 'static, O: OffsetSize> FieldValues<O> for TiffTypeValues<T, O> {
    fn count(&self) -> O {
        O::from_usize(self.values.len())
    }

    fn size(&self) -> O {
        T::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor<O>) -> Box<dyn AllocatedFieldValues<O>> {
        let position = if self.size().to_u64() <= O::INLINE_THRESHOLD.to_u64() {
            None
        } else {
            let size = self.size() + self.size() % O::TWO;
            let pos = c.allocated_bytes();
            c.allocate(size);
            Some(pos)
        };

        Box::new(AllocatedTiffTypeValues {
            position,
            values: self.values,
            _phantom: PhantomData,
        })
    }
}

/// Allocated form of `TiffTypeValues`
struct AllocatedTiffTypeValues<T, O: OffsetSize> {
    position: Option<O>,
    values: Vec<T>,
    _phantom: PhantomData<O>,
}

impl<T: TiffType<O>, O: OffsetSize> AllocatedFieldValues<O> for AllocatedTiffTypeValues<T, O> {
    fn count(&self) -> O {
        O::from_usize(self.values.len())
    }

    fn size(&self) -> O {
        T::size() * self.count()
    }

    fn position(&self) -> Option<O> {
        self.position
    }

    fn type_id(&self) -> u16 {
        T::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let size = self.size();
        for value in self.values {
            let file_initial = file.written_bytes();
            value.write_to(file)?;
            let written_size = file.written_bytes() - file_initial;
            if written_size != T::size().to_u64() {
                panic!(
                    "The size indicated ({}) is different from the number of bytes the type has written to the file ({}).",
                    T::size().to_u64(),
                    written_size
                )
            }
        }

        if size.to_u64() % 2 == 1 && size.to_u64() > O::INLINE_THRESHOLD.to_u64() {
            file.write_arbitrary_byte()?;
        }
        Ok(())
    }
}

/// A list of [`IFD`] values, each pointing to a specific [`Ifd`].
///
/// Generic over `O: OffsetSize` to support both TIFF (u32) and BigTIFF (u64).
///
/// This structure owns a list of [`IfdChain`]s instead, so the user
/// doesn't have to deal with the offsets in the file. Each [`IFD`]
/// value will point to the first element of each [`IfdChain`]. Each
/// of those `Ifd`s will point to the next one in their chain (if they
/// are not the last of their chain) and so on.
///
/// It is responsible for writing both the offsets and all the [`Ifd`]s.
///
/// [`LONG`]: ../types/struct.LONG.html
/// [`IFD`]: ../types/struct.IFD.html
/// [`Ifd`]: ../struct.Ifd.html
/// [`IfdChain`]: ../struct.IfdChain.html
pub struct OffsetsToIfds<O: OffsetSize = u32> {
    pub data: Vec<IfdChain<O>>,
}

impl<O: OffsetSize> OffsetsToIfds<O> {
    /// Creates a new `OffsetsToIfds` instance from a vector of [`IfdChain`]s.
    ///
    /// [`IfdChain`]: ../struct.IfdChain.html
    pub fn new(ifds: Vec<IfdChain<O>>) -> Self {
        OffsetsToIfds { data: ifds }
    }
}

impl FieldValues<u32> for OffsetsToIfds<u32> {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        <IFD as TiffType<u32>>::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor<u32>) -> Box<dyn AllocatedFieldValues<u32>> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            let offsets = Vec::new();
            let ifd = self.data.into_iter().next().unwrap();
            let allocated_data = vec![ifd.allocate(c)];

            Box::new(AllocatedOffsetsToIfds {
                position,
                offsets,
                data: allocated_data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());
            let mut allocated_data = Vec::with_capacity(self.data.len());

            for ifd in self.data {
                offsets.push(IFD(c.allocated_bytes()));
                allocated_data.push(ifd.allocate(c));
            }

            Box::new(AllocatedOffsetsToIfds {
                position,
                offsets,
                data: allocated_data,
            })
        }
    }
}

impl FieldValues<u64> for OffsetsToIfds<u64> {
    fn count(&self) -> u64 {
        self.data.len() as u64
    }

    fn size(&self) -> u64 {
        <BIGIFD as TiffType<u64>>::size() * self.count()
    }

    fn allocate(self: Box<Self>, c: &mut Cursor<u64>) -> Box<dyn AllocatedFieldValues<u64>> {
        let position = Some(c.allocated_bytes());
        if self.data.len() == 1 {
            let offsets = Vec::new();
            let ifd = self.data.into_iter().next().unwrap();
            let allocated_data = vec![ifd.allocate(c)];

            Box::new(AllocatedOffsetsToIfds64 {
                position,
                offsets,
                data: allocated_data,
            })
        } else {
            c.allocate(self.size());
            let mut offsets = Vec::with_capacity(self.data.len());
            let mut allocated_data = Vec::with_capacity(self.data.len());

            for ifd in self.data {
                offsets.push(BIGIFD(c.allocated_bytes()));
                allocated_data.push(ifd.allocate(c));
            }

            Box::new(AllocatedOffsetsToIfds64 {
                position,
                offsets,
                data: allocated_data,
            })
        }
    }
}

/// Allocated form of `OffsetsToIfds` for u32
struct AllocatedOffsetsToIfds {
    position: Option<u32>,
    offsets: Vec<IFD>,
    data: Vec<AllocatedIfdChain<u32>>,
}

impl AllocatedFieldValues<u32> for AllocatedOffsetsToIfds {
    fn count(&self) -> u32 {
        self.data.len() as u32
    }

    fn size(&self) -> u32 {
        <IFD as TiffType<u32>>::size() * self.count()
    }

    fn position(&self) -> Option<u32> {
        self.position
    }

    fn type_id(&self) -> u16 {
        <IFD as TiffType<u32>>::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let AllocatedOffsetsToIfds { data, offsets, .. } = unboxed;
        for offset in offsets {
            <IFD as TiffType<u32>>::write_to(offset, file)?;
        }
        for ifd in data.into_iter() {
            ifd.write_to(file)?;
        }
        Ok(())
    }
}

/// Allocated form of `OffsetsToIfds` for u64
struct AllocatedOffsetsToIfds64 {
    position: Option<u64>,
    offsets: Vec<BIGIFD>,
    data: Vec<AllocatedIfdChain<u64>>,
}

impl AllocatedFieldValues<u64> for AllocatedOffsetsToIfds64 {
    fn count(&self) -> u64 {
        self.data.len() as u64
    }

    fn size(&self) -> u64 {
        <BIGIFD as TiffType<u64>>::size() * self.count()
    }

    fn position(&self) -> Option<u64> {
        self.position
    }

    fn type_id(&self) -> u16 {
        <BIGIFD as TiffType<u64>>::id()
    }

    fn write_to(self: Box<Self>, file: &mut EndianFile) -> io::Result<()> {
        let unboxed = *self;
        let AllocatedOffsetsToIfds64 { data, offsets, .. } = unboxed;
        for offset in offsets {
            <BIGIFD as TiffType<u64>>::write_to(offset, file)?;
        }
        for ifd in data.into_iter() {
            ifd.write_to(file)?;
        }
        Ok(())
    }
}
