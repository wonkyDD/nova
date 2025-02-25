// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

use crate::{
    ecmascript::{
        abstract_operations::{
            operations_on_objects::{call_function, try_get},
            testing_and_comparison::{is_array, is_callable, same_value_zero},
            type_conversion::{
                to_boolean, to_integer_or_infinity, to_string, try_to_integer_or_infinity,
                try_to_string,
            },
        },
        builders::{
            builtin_function_builder::BuiltinFunctionBuilder,
            ordinary_object_builder::OrdinaryObjectBuilder,
        },
        builtins::{
            array_buffer::{get_value_from_buffer, is_detached_buffer, Ordering},
            indexed_collections::array_objects::array_iterator_objects::array_iterator::{
                ArrayIterator, CollectionIteratorKind,
            },
            typed_array::TypedArray,
            ArgumentsList, Behaviour, Builtin, BuiltinGetter, BuiltinIntrinsic,
            BuiltinIntrinsicConstructor,
        },
        execution::{agent::ExceptionType, Agent, JsResult, RealmIdentifier},
        types::{
            IntoObject, IntoValue, Number, Object, PropertyKey, String, U8Clamped, Value,
            BUILTIN_STRING_MEMORY,
        },
    },
    engine::{
        context::{GcScope, NoGcScope},
        unwrap_try, TryResult,
    },
    heap::{IntrinsicConstructorIndexes, IntrinsicFunctionIndexes, WellKnownSymbolIndexes},
    SmallInteger,
};

use super::abstract_operations::is_typed_array_out_of_bounds;
use super::abstract_operations::make_typed_array_with_buffer_witness_record;
use super::abstract_operations::typed_array_byte_length;
use super::abstract_operations::typed_array_length;
use super::abstract_operations::validate_typed_array;

pub struct TypedArrayIntrinsicObject;

impl Builtin for TypedArrayIntrinsicObject {
    const BEHAVIOUR: Behaviour = Behaviour::Constructor(Self::constructor);
    const LENGTH: u8 = 0;
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.TypedArray;
}
impl BuiltinIntrinsicConstructor for TypedArrayIntrinsicObject {
    const INDEX: IntrinsicConstructorIndexes = IntrinsicConstructorIndexes::TypedArray;
}

struct TypedArrayFrom;
impl Builtin for TypedArrayFrom {
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayIntrinsicObject::from);
    const LENGTH: u8 = 1;
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.from;
}
struct TypedArrayOf;
impl Builtin for TypedArrayOf {
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayIntrinsicObject::of);
    const LENGTH: u8 = 0;
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.fromCodePoint;
}
struct TypedArrayGetSpecies;
impl Builtin for TypedArrayGetSpecies {
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayIntrinsicObject::get_species);
    const LENGTH: u8 = 0;
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get__Symbol_species_;
    const KEY: Option<PropertyKey<'static>> =
        Some(WellKnownSymbolIndexes::Species.to_property_key());
}
impl BuiltinGetter for TypedArrayGetSpecies {}
impl TypedArrayIntrinsicObject {
    fn constructor(
        agent: &mut Agent,
        _this_value: Value,
        _arguments: ArgumentsList,
        _new_target: Option<Object>,
        gc: GcScope,
    ) -> JsResult<Value> {
        Err(agent.throw_exception_with_static_message(
            crate::ecmascript::execution::agent::ExceptionType::TypeError,
            "Abstract class TypedArray not directly constructable",
            gc.nogc(),
        ))
    }

    fn from(
        _agent: &mut Agent,
        _this_value: Value,
        _arguments: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn is_array(
        agent: &mut Agent,
        _this_value: Value,
        arguments: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        is_array(agent, arguments.get(0), gc.nogc()).map(Value::Boolean)
    }

    fn of(
        _agent: &mut Agent,
        _this_value: Value,
        _arguments: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn get_species(
        _: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        Ok(this_value)
    }

    pub(crate) fn create_intrinsic(agent: &mut Agent, realm: RealmIdentifier) {
        let intrinsics = agent.get_realm(realm).intrinsics();
        let typed_array_prototype = intrinsics.typed_array_prototype();

        BuiltinFunctionBuilder::new_intrinsic_constructor::<TypedArrayIntrinsicObject>(
            agent, realm,
        )
        .with_property_capacity(4)
        .with_builtin_function_property::<TypedArrayFrom>()
        .with_builtin_function_property::<TypedArrayOf>()
        .with_prototype_property(typed_array_prototype.into_object())
        .with_builtin_function_getter_property::<TypedArrayGetSpecies>()
        .build();
    }
}

pub(crate) struct TypedArrayPrototype;

struct TypedArrayPrototypeAt;
impl Builtin for TypedArrayPrototypeAt {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.at;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::at);
}
struct TypedArrayPrototypeGetBuffer;
impl Builtin for TypedArrayPrototypeGetBuffer {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get_buffer;
    const KEY: Option<PropertyKey<'static>> = Some(BUILTIN_STRING_MEMORY.buffer.to_property_key());
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::get_buffer);
}
impl BuiltinGetter for TypedArrayPrototypeGetBuffer {}
struct TypedArrayPrototypeGetByteLength;
impl Builtin for TypedArrayPrototypeGetByteLength {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get_byteLength;
    const KEY: Option<PropertyKey<'static>> =
        Some(BUILTIN_STRING_MEMORY.byteLength.to_property_key());
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::get_byte_length);
}
impl BuiltinGetter for TypedArrayPrototypeGetByteLength {}
struct TypedArrayPrototypeGetByteOffset;
impl Builtin for TypedArrayPrototypeGetByteOffset {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get_byteOffset;
    const KEY: Option<PropertyKey<'static>> =
        Some(BUILTIN_STRING_MEMORY.byteOffset.to_property_key());
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::get_byte_offset);
}
impl BuiltinGetter for TypedArrayPrototypeGetByteOffset {}
struct TypedArrayPrototypeCopyWithin;
impl Builtin for TypedArrayPrototypeCopyWithin {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.copyWithin;
    const LENGTH: u8 = 2;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::copy_within);
}
struct TypedArrayPrototypeEntries;
impl Builtin for TypedArrayPrototypeEntries {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.entries;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::entries);
}
struct TypedArrayPrototypeEvery;
impl Builtin for TypedArrayPrototypeEvery {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.every;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::every);
}
struct TypedArrayPrototypeFill;
impl Builtin for TypedArrayPrototypeFill {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.fill;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::fill);
}
struct TypedArrayPrototypeFilter;
impl Builtin for TypedArrayPrototypeFilter {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.filter;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::filter);
}
struct TypedArrayPrototypeFind;
impl Builtin for TypedArrayPrototypeFind {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.find;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::find);
}
struct TypedArrayPrototypeFindIndex;
impl Builtin for TypedArrayPrototypeFindIndex {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.findIndex;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::find_index);
}
struct TypedArrayPrototypeFindLast;
impl Builtin for TypedArrayPrototypeFindLast {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.findLast;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::find_last);
}
struct TypedArrayPrototypeFindLastIndex;
impl Builtin for TypedArrayPrototypeFindLastIndex {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.findLastIndex;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::find_last_index);
}
struct TypedArrayPrototypeForEach;
impl Builtin for TypedArrayPrototypeForEach {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.forEach;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::for_each);
}
struct TypedArrayPrototypeIncludes;
impl Builtin for TypedArrayPrototypeIncludes {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.includes;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::includes);
}
struct TypedArrayPrototypeIndexOf;
impl Builtin for TypedArrayPrototypeIndexOf {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.indexOf;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::index_of);
}
struct TypedArrayPrototypeJoin;
impl Builtin for TypedArrayPrototypeJoin {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.join;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::join);
}
struct TypedArrayPrototypeKeys;
impl Builtin for TypedArrayPrototypeKeys {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.keys;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::keys);
}
struct TypedArrayPrototypeLastIndexOf;
impl Builtin for TypedArrayPrototypeLastIndexOf {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.lastIndexOf;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::last_index_of);
}
struct TypedArrayPrototypeGetLength;
impl Builtin for TypedArrayPrototypeGetLength {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get_length;
    const KEY: Option<PropertyKey<'static>> = Some(BUILTIN_STRING_MEMORY.length.to_property_key());
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::get_length);
}
impl BuiltinGetter for TypedArrayPrototypeGetLength {}
struct TypedArrayPrototypeMap;
impl Builtin for TypedArrayPrototypeMap {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.map;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::map);
}
struct TypedArrayPrototypeReduce;
impl Builtin for TypedArrayPrototypeReduce {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.reduce;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::reduce);
}
struct TypedArrayPrototypeReduceRight;
impl Builtin for TypedArrayPrototypeReduceRight {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.reduceRight;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::reduce_right);
}
struct TypedArrayPrototypeReverse;
impl Builtin for TypedArrayPrototypeReverse {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.reverse;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::reverse);
}
struct TypedArrayPrototypeSet;
impl Builtin for TypedArrayPrototypeSet {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.set;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::set);
}
struct TypedArrayPrototypeSlice;
impl Builtin for TypedArrayPrototypeSlice {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.slice;
    const LENGTH: u8 = 2;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::slice);
}
struct TypedArrayPrototypeSome;
impl Builtin for TypedArrayPrototypeSome {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.some;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::some);
}
struct TypedArrayPrototypeSort;
impl Builtin for TypedArrayPrototypeSort {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.sort;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::sort);
}
struct TypedArrayPrototypeSubarray;
impl Builtin for TypedArrayPrototypeSubarray {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.subarray;
    const LENGTH: u8 = 2;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::subarray);
}
struct TypedArrayPrototypeToLocaleString;
impl Builtin for TypedArrayPrototypeToLocaleString {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.toLocaleString;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::to_locale_string);
}
struct TypedArrayPrototypeToReversed;
impl Builtin for TypedArrayPrototypeToReversed {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.toReversed;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::to_reversed);
}
struct TypedArrayPrototypeToSorted;
impl Builtin for TypedArrayPrototypeToSorted {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.toSorted;
    const LENGTH: u8 = 1;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::to_sorted);
}
struct TypedArrayPrototypeValues;
impl Builtin for TypedArrayPrototypeValues {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.values;
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::values);
}
impl BuiltinIntrinsic for TypedArrayPrototypeValues {
    const INDEX: IntrinsicFunctionIndexes = IntrinsicFunctionIndexes::TypedArrayPrototypeValues;
}
struct TypedArrayPrototypeWith;
impl Builtin for TypedArrayPrototypeWith {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.with;
    const LENGTH: u8 = 2;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::with);
}
struct TypedArrayPrototypeGetToStringTag;
impl Builtin for TypedArrayPrototypeGetToStringTag {
    const NAME: String<'static> = BUILTIN_STRING_MEMORY.get__Symbol_toStringTag_;
    const KEY: Option<PropertyKey<'static>> =
        Some(WellKnownSymbolIndexes::ToStringTag.to_property_key());
    const LENGTH: u8 = 0;
    const BEHAVIOUR: Behaviour = Behaviour::Regular(TypedArrayPrototype::get_to_string_tag);
}
impl BuiltinGetter for TypedArrayPrototypeGetToStringTag {}

impl TypedArrayPrototype {
    /// ### [23.2.3.1 %TypedArray%.prototype.at ( index )](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-array.prototype.at)
    fn at(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let index = arguments.get(0);
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        let mut o = ta_record.object;
        // 3. Let len be TypedArrayLength(taRecord).
        let len = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<u8>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_length::<u16>(agent, &ta_record, gc.nogc())
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
            TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_)
            | TypedArray::Float32Array(_) => {
                typed_array_length::<u32>(agent, &ta_record, gc.nogc())
            }
            TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_)
            | TypedArray::Float64Array(_) => {
                typed_array_length::<u64>(agent, &ta_record, gc.nogc())
            }
        } as i64;
        // 4. Let relativeIndex be ? ToIntegerOrInfinity(index).
        let relative_index = if let Value::Integer(index) = index {
            index.into_i64()
        } else {
            let scoped_o = o.scope(agent, gc.nogc());
            let result = to_integer_or_infinity(agent, index, gc.reborrow())?.into_i64();
            o = scoped_o.get(agent).bind(gc.nogc());
            result
        };
        // 5. If relativeIndex ≥ 0, then
        let k = if relative_index >= 0 {
            // a. Let k be relativeIndex.
            relative_index
        } else {
            // 6. Else,
            // a. Let k be len + relativeIndex.
            len + relative_index
        };
        // 7. If k < 0 or k ≥ len, return undefined.
        if k < 0 || k >= len {
            return Ok(Value::Undefined);
        };
        // 8. Return ! Get(O, ! ToString(𝔽(k))).
        Ok(unwrap_try(try_get(
            agent,
            o,
            PropertyKey::Integer(k.try_into().unwrap()),
            gc.nogc(),
        )))
    }

    /// ### [23.2.3.2 get %TypedArray%.prototype.buffer](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.buffer)
    ///
    /// %TypedArray%.prototype.buffer is an accessor property whose set accessor
    /// function is undefined.
    fn get_buffer(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        let gc = gc.into_nogc();
        // 1. Let O be the this value.
        // 2. Perform ? RequireInternalSlot(O, [[TypedArrayName]]).
        // 3. Assert: O has a [[ViewedArrayBuffer]] internal slot.
        // 4. Let buffer be O.[[ViewedArrayBuffer]].
        let o = require_internal_slot_typed_array(agent, this_value, gc)?;

        // 5. Return buffer.
        Ok(o.get_viewed_array_buffer(agent, gc).into_value())
    }

    /// ### [23.2.3.3 get %TypedArray%.prototype.byteLength](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.bytelength)
    ///
    /// %TypedArray%.prototype.byteLength is an accessor property whose set
    /// accessor function is undefined.
    fn get_byte_length(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        let gc = gc.into_nogc();
        // 1. Let O be the this value.
        // 2. Perform ? RequireInternalSlot(O, [[TypedArrayName]]).
        // 3. Assert: O has a [[ViewedArrayBuffer]] internal slot.
        let o = require_internal_slot_typed_array(agent, this_value, gc)?;

        // 4. Let taRecord be MakeTypedArrayWithBufferWitnessRecord(O, seq-cst).
        let ta_record = make_typed_array_with_buffer_witness_record(agent, o, Ordering::SeqCst, gc);

        // 5. Let size be TypedArrayByteLength(taRecord).
        let size = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_byte_length::<u8>(agent, &ta_record, gc)
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_byte_length::<u16>(agent, &ta_record, gc)
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_byte_length::<f16>(agent, &ta_record, gc),
            TypedArray::Float32Array(_)
            | TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_) => typed_array_byte_length::<u32>(agent, &ta_record, gc),
            TypedArray::Float64Array(_)
            | TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_) => {
                typed_array_byte_length::<u64>(agent, &ta_record, gc)
            }
        };

        // 6. Return 𝔽(size).
        Ok(Value::try_from(size as i64).unwrap())
    }

    /// ### [23.2.3.4 get %TypedArray%.prototype.byteOffset](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.byteoffset)
    ///
    /// %TypedArray%.prototype.byteOffset is an accessor property whose set
    /// accessor function is undefined.
    fn get_byte_offset(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        let gc = gc.into_nogc();
        // 1. Let O be the this value.
        // 2. Perform ? RequireInternalSlot(O, [[TypedArrayName]]).
        // 3. Assert: O has a [[ViewedArrayBuffer]] internal slot.
        let o = require_internal_slot_typed_array(agent, this_value, gc)?;

        // 4. Let taRecord be MakeTypedArrayWithBufferWitnessRecord(O, seq-cst).
        let ta_record = make_typed_array_with_buffer_witness_record(agent, o, Ordering::SeqCst, gc);

        // 5. If IsTypedArrayOutOfBounds(taRecord) is true, return +0𝔽.
        if match o {
            TypedArray::Int8Array(_) => is_typed_array_out_of_bounds::<i8>(agent, &ta_record, gc),
            TypedArray::Uint8Array(_) => is_typed_array_out_of_bounds::<u8>(agent, &ta_record, gc),
            TypedArray::Uint8ClampedArray(_) => {
                is_typed_array_out_of_bounds::<U8Clamped>(agent, &ta_record, gc)
            }
            TypedArray::Int16Array(_) => is_typed_array_out_of_bounds::<i16>(agent, &ta_record, gc),
            TypedArray::Uint16Array(_) => {
                is_typed_array_out_of_bounds::<u16>(agent, &ta_record, gc)
            }
            TypedArray::Int32Array(_) => is_typed_array_out_of_bounds::<i32>(agent, &ta_record, gc),
            TypedArray::Uint32Array(_) => {
                is_typed_array_out_of_bounds::<u32>(agent, &ta_record, gc)
            }
            TypedArray::BigInt64Array(_) => {
                is_typed_array_out_of_bounds::<i64>(agent, &ta_record, gc)
            }
            TypedArray::BigUint64Array(_) => {
                is_typed_array_out_of_bounds::<u64>(agent, &ta_record, gc)
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => {
                is_typed_array_out_of_bounds::<f16>(agent, &ta_record, gc)
            }
            TypedArray::Float32Array(_) => {
                is_typed_array_out_of_bounds::<f32>(agent, &ta_record, gc)
            }
            TypedArray::Float64Array(_) => {
                is_typed_array_out_of_bounds::<f64>(agent, &ta_record, gc)
            }
        } {
            return Ok(Value::pos_zero());
        }

        // 6. Let offset be O.[[ByteOffset]].
        // 7. Return 𝔽(offset).
        Ok(Value::try_from(o.byte_offset(agent) as i64).unwrap())
    }

    fn copy_within(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    /// ### [23.2.3.7 %TypedArray%.prototype.entries ( )](https://tc39.es/ecma262/#sec-%typedarray%.prototype.entries)
    fn entries(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        // 1. Let O be the this value.
        // 2. Perform ? ValidateTypedArray(O, seq-cst).
        let o = validate_typed_array(agent, this_value, Ordering::SeqCst, gc.nogc())?.object;
        // 3. Return CreateArrayIterator(O, key+value).
        Ok(
            ArrayIterator::from_object(agent, o.into_object(), CollectionIteratorKind::KeyAndValue)
                .into_value(),
        )
    }

    // ### [23.2.3.8 %%TypedArray%.prototype.every ( callback [ , thisArg ] )](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-%typedarray%.prototype.every)
    fn every(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let callback = arguments.get(0).bind(gc.nogc());
        let this_arg = arguments.get(1).bind(gc.nogc());
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        let mut o = ta_record.object;
        // 3. Let len be TypedArrayLength(taRecord).
        let len = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<u8>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_length::<u16>(agent, &ta_record, gc.nogc())
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
            TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_)
            | TypedArray::Float32Array(_) => {
                typed_array_length::<u32>(agent, &ta_record, gc.nogc())
            }
            TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_)
            | TypedArray::Float64Array(_) => {
                typed_array_length::<u64>(agent, &ta_record, gc.nogc())
            }
        };
        // 4. If IsCallable(callback) is false, throw a TypeError exception.
        let Some(callback) = is_callable(callback, gc.nogc()) else {
            return Err(agent.throw_exception_with_static_message(
                ExceptionType::TypeError,
                "Callback is not callable",
                gc.nogc(),
            ));
        };
        let callback = callback.scope(agent, gc.nogc());
        let scoped_o = o.scope(agent, gc.nogc());
        // 5. Let k be 0.
        let mut k = 0;
        // 6. Repeat, while k < len,
        while k < len {
            // a. Let Pk be ! ToString(𝔽(k)).
            let pk = PropertyKey::from(SmallInteger::from(k as u32));
            // b. Let kValue be ! Get(O, Pk).
            let k_value = unwrap_try(try_get(agent, o, pk, gc.nogc()));
            // c. Let testResult be ToBoolean(? Call(callback, thisArg, « kValue, 𝔽(k), O »)).
            let call = call_function(
                agent,
                callback.get(agent),
                this_arg,
                Some(ArgumentsList(&[
                    k_value,
                    Number::try_from(k).unwrap().into_value(),
                    o.into_value(),
                ])),
                gc.reborrow(),
            )?;
            let test_result = to_boolean(agent, call);
            // d. If testResult is false, return false.
            if !test_result {
                return Ok(false.into());
            }
            // e. Set k to k + 1.
            o = scoped_o.get(agent).bind(gc.nogc());
            k += 1;
        }
        // 7. Return true.
        Ok(true.into())
    }

    fn fill(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn filter(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn find(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn find_index(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn find_last(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn find_last_index(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    // ### [ 23.2.3.15 %TypedArray%.prototype.forEach ( callback [ , thisArg ] )](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-%typedarray%.prototype.foreach)
    // The interpretation and use of the arguments of this method are the same as for Array.prototype.forEach as defined in 23.1.3.15.
    fn for_each(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let callback = arguments.get(0).bind(gc.nogc());
        let this_arg = arguments.get(1).bind(gc.nogc());
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        // 3. Let len be TypedArrayLength(taRecord).
        let mut o = ta_record.object;
        let scoped_o = o.scope(agent, gc.nogc());
        let len = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<u8>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_length::<u16>(agent, &ta_record, gc.nogc())
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
            TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_)
            | TypedArray::Float32Array(_) => {
                typed_array_length::<u32>(agent, &ta_record, gc.nogc())
            }
            TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_)
            | TypedArray::Float64Array(_) => {
                typed_array_length::<u64>(agent, &ta_record, gc.nogc())
            }
        };
        // 4. If IsCallable(callback) is false, throw a TypeError exception.
        let Some(callback) = is_callable(callback, gc.nogc()) else {
            return Err(agent.throw_exception_with_static_message(
                ExceptionType::TypeError,
                "Callback is not callable",
                gc.nogc(),
            ));
        };
        let callback = callback.scope(agent, gc.nogc());
        // 5. Let k be 0.
        let mut k = 0;
        // 6. Repeat, while k < len,
        while k < len {
            // a. Let Pk be ! ToString(𝔽(k)).
            let pk: PropertyKey = k.try_into().unwrap();
            // b. Let kValue be ! Get(O, Pk).
            let k_value = unwrap_try(try_get(agent, o, pk, gc.nogc()));
            // c. Perform ? Call(callback, thisArg, « kValue, 𝔽(k), O »).
            // // SAFETY: pk is Integer, which is what we want for fk as well.
            let fk = unsafe { pk.into_value_unchecked() };
            call_function(
                agent,
                callback.get(agent),
                this_arg,
                Some(ArgumentsList(&[k_value, fk, o.into_value()])),
                gc.reborrow(),
            )?;
            // d. Set k to k + 1.
            k += 1;
            o = scoped_o.get(agent).bind(gc.nogc());
        }
        // 7. Return undefined.
        Ok(Value::Undefined)
    }

    // ### [23.2.3.16 %TypedArray%.prototype.includes ( searchElement [ , fromIndex ] )](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-%typedarray%.prototype.includes)
    // The interpretation and use of the arguments of this method are the same as for Array.prototype.includes as defined in 23.1.3.16.
    fn includes(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let search_element = arguments.get(0).bind(gc.nogc());
        let from_index = arguments.get(1).bind(gc.nogc());
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        // 3. Let len be TypedArrayLength(taRecord).
        let mut o = ta_record.object;
        let len = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<u8>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_length::<u16>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_)
            | TypedArray::Float32Array(_) => {
                typed_array_length::<u32>(agent, &ta_record, gc.nogc())
            }
            TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_)
            | TypedArray::Float64Array(_) => {
                typed_array_length::<u64>(agent, &ta_record, gc.nogc())
            }
        } as i64;
        // 4. If len = 0, return false.
        if len == 0 {
            return Ok(false.into());
        };
        // 5. Let n be ? ToIntegerOrInfinity(fromIndex).
        let n = if let TryResult::Continue(n) =
            try_to_integer_or_infinity(agent, from_index, gc.nogc())
        {
            n?
        } else {
            let scoped_o = o.scope(agent, gc.nogc());
            let result = to_integer_or_infinity(agent, from_index, gc.reborrow());
            o = scoped_o.get(agent).bind(gc.nogc());
            result?
        };
        // 6. Assert: If fromIndex is undefined, then n is 0.
        if from_index.is_undefined() {
            assert_eq!(n.into_i64(), 0);
        }
        // 7. If n = +∞, return false.
        let n = if n.is_pos_infinity() {
            return Ok(false.into());
        } else if n.is_neg_infinity() {
            // 8. Else if n = -∞, set n to 0.
            0
        } else {
            n.into_i64()
        };
        // 9. If n ≥ 0, then
        let mut k = if n >= 0 {
            // a. Let k be n.
            n
        } else {
            // 10. Else,
            // a. Let k be len + n.
            let k = len + n;
            // b. If k < 0, set k to 0.
            if k < 0 {
                0
            } else {
                k
            }
        };
        // 11. Repeat, while k < len,
        while k < len {
            // a. Let elementK be ! Get(O, ! ToString(𝔽(k))).
            let element_k = unwrap_try(try_get(
                agent,
                o,
                PropertyKey::Integer(k.try_into().unwrap()),
                gc.nogc(),
            ));
            // b. If SameValueZero(searchElement, elementK) is true, return true.
            if same_value_zero(agent, search_element, element_k) {
                return Ok(true.into());
            }
            // c. Set k to k + 1.
            k += 1
        }
        // 12. Return false.
        Ok(false.into())
    }

    fn index_of(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    /// ### [23.2.3.18 %TypedArray%.prototype.join ( separator )](https://tc39.es/ecma262/#sec-%typedarray%.prototype.join)
    ///
    /// The interpretation and use of the arguments of this method are the
    /// same as for Array.prototype.join as defined in 23.1.3.18.
    ///
    /// This method is not generic. The this value must be an object with a
    /// `[[TypedArrayName]]` internal slot.
    fn join(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let separator = arguments.get(0);
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        let mut o = ta_record.object;
        // 3. Let len be TypedArrayLength(taRecord).
        let (len, element_size) = match o {
            TypedArray::Int8Array(_) => (
                typed_array_length::<i8>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<i8>(),
            ),
            TypedArray::Uint8Array(_) => (
                typed_array_length::<u8>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<u8>(),
            ),
            TypedArray::Uint8ClampedArray(_) => (
                typed_array_length::<U8Clamped>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<U8Clamped>(),
            ),
            TypedArray::Int16Array(_) => (
                typed_array_length::<i16>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<i16>(),
            ),
            TypedArray::Uint16Array(_) => (
                typed_array_length::<u16>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<u16>(),
            ),
            TypedArray::Int32Array(_) => (
                typed_array_length::<i32>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<i32>(),
            ),
            TypedArray::Uint32Array(_) => (
                typed_array_length::<u32>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<u32>(),
            ),
            TypedArray::BigInt64Array(_) => (
                typed_array_length::<i64>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<i64>(),
            ),
            TypedArray::BigUint64Array(_) => (
                typed_array_length::<u64>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<u64>(),
            ),
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => (
                typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<f16>(),
            ),
            TypedArray::Float32Array(_) => (
                typed_array_length::<f32>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<f32>(),
            ),
            TypedArray::Float64Array(_) => (
                typed_array_length::<f64>(agent, &ta_record, gc.nogc()),
                std::mem::size_of::<f64>(),
            ),
        };
        // 4. If separator is undefined, let sep be ",".
        let (sep_string, recheck_buffer) = if separator.is_undefined() {
            (String::from_small_string(","), false)
        } else if let Ok(sep) = String::try_from(separator) {
            (sep, false)
        } else {
            // 5. Else, let sep be ? ToString(separator).
            let scoped_o = o.scope(agent, gc.nogc());
            let result = to_string(agent, separator, gc.reborrow())?
                .unbind()
                .bind(gc.nogc());
            o = scoped_o.get(agent).bind(gc.nogc());
            (result, true)
        };
        if len == 0 {
            return Ok(String::EMPTY_STRING.into_value());
        }
        let owned_sep = match &sep_string {
            String::String(heap_string) => Some(heap_string.as_str(agent).to_owned()),
            String::SmallString(_) => None,
        };
        let sep = match &owned_sep {
            Some(str_data) => str_data.as_str(),
            None => {
                let String::SmallString(sep) = &sep_string else {
                    unreachable!();
                };
                sep.as_str()
            }
        };
        // 6. Let R be the empty String.
        let mut r = std::string::String::with_capacity(len * 3);
        // 7. Let k be 0.
        // 8. Repeat, while k < len,
        let offset = o.byte_offset(agent);
        let viewed_array_buffer = o.get_viewed_array_buffer(agent, gc.nogc());
        // Note: Above ToString might have detached the ArrayBuffer or shrunk its length.
        let (is_invalid_typed_array, after_len) = if recheck_buffer {
            let is_detached = is_detached_buffer(agent, viewed_array_buffer);
            let ta_record = make_typed_array_with_buffer_witness_record(
                agent,
                o,
                Ordering::Unordered,
                gc.nogc(),
            );
            match o {
                TypedArray::Int8Array(_) => (
                    is_detached || is_typed_array_out_of_bounds::<i8>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<i8>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Uint8Array(_) => (
                    is_detached || is_typed_array_out_of_bounds::<u8>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<u8>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Uint8ClampedArray(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<U8Clamped>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<U8Clamped>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Int16Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<i16>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<i16>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Uint16Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<u16>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<u16>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Int32Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<i32>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<i32>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Uint32Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<u32>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<u32>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::BigInt64Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<i64>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<i64>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::BigUint64Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<u64>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<u64>(agent, &ta_record, gc.nogc()),
                ),
                #[cfg(feature = "proposal-float16array")]
                TypedArray::Float16Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<f16>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Float32Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<f32>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<f32>(agent, &ta_record, gc.nogc()),
                ),
                TypedArray::Float64Array(_) => (
                    is_detached
                        || is_typed_array_out_of_bounds::<f64>(agent, &ta_record, gc.nogc()),
                    typed_array_length::<f64>(agent, &ta_record, gc.nogc()),
                ),
            }
        } else {
            // Note: Growable SharedArrayBuffers are a thing, and can change the
            // length at any point in time but they can never shrink the buffer.
            // Hence the TypedArray or any of its indexes rae never invalidated.
            (false, len)
        };
        for k in 0..len {
            // a. If k > 0, set R to the string-concatenation of R and sep.
            if k > 0 {
                r.push_str(sep);
            }
            // c. If element is not undefined, then
            if is_invalid_typed_array || k >= after_len {
                // Note: element is undefined if the ViewedArrayBuffer was
                // detached by ToString call, or was shrunk to less than len.
                continue;
            }
            let byte_index_in_buffer = k * element_size + offset;
            // b. Let element be ! Get(O, ! ToString(𝔽(k))).
            let element = match o {
                TypedArray::Int8Array(_) => get_value_from_buffer::<i8>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Uint8Array(_) => get_value_from_buffer::<u8>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Uint8ClampedArray(_) => get_value_from_buffer::<U8Clamped>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Int16Array(_) => get_value_from_buffer::<i16>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Uint16Array(_) => get_value_from_buffer::<u16>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Int32Array(_) => get_value_from_buffer::<i32>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Uint32Array(_) => get_value_from_buffer::<u32>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::BigInt64Array(_) => get_value_from_buffer::<i64>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::BigUint64Array(_) => get_value_from_buffer::<u64>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                #[cfg(feature = "proposal-float16array")]
                TypedArray::Float16Array(_) => get_value_from_buffer::<f16>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Float32Array(_) => get_value_from_buffer::<f32>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
                TypedArray::Float64Array(_) => get_value_from_buffer::<f64>(
                    agent,
                    viewed_array_buffer,
                    byte_index_in_buffer,
                    true,
                    Ordering::Unordered,
                    None,
                    gc.nogc(),
                ),
            };
            // i. Let S be ! ToString(element).
            let s = unwrap_try(try_to_string(agent, element, gc.nogc())).unwrap();
            // ii. Set R to the string-concatenation of R and S.
            r.push_str(s.as_str(agent));
            // d. Set k to k + 1.
        }
        // 9. Return R.
        Ok(String::from_string(agent, r, gc.nogc()).into_value())
    }

    /// ### [23.2.3.19 %TypedArray%.prototype.keys ( )](https://tc39.es/ecma262/#sec-%typedarray%.prototype.keys)
    fn keys(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        // 1. Let O be the this value.
        // 2. Perform ? ValidateTypedArray(O, seq-cst).
        let o = validate_typed_array(agent, this_value, Ordering::SeqCst, gc.nogc())?.object;
        // 3. Return CreateArrayIterator(O, key).
        Ok(
            ArrayIterator::from_object(agent, o.into_object(), CollectionIteratorKind::Key)
                .into_value(),
        )
    }

    fn last_index_of(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    /// ### [23.2.3.21 get %TypedArray%.prototype.length](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype.length)
    fn get_length(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        let gc = gc.into_nogc();
        // 1. Let O be the this value.
        // 2. Perform ? RequireInternalSlot(O, [[TypedArrayName]]).
        // 3. Assert: O has [[ViewedArrayBuffer]] and [[ArrayLength]] internal slots.
        let o = require_internal_slot_typed_array(agent, this_value, gc)?;
        // 4. Let taRecord be MakeTypedArrayWithBufferWitnessRecord(O, seq-cst).
        let ta_record = make_typed_array_with_buffer_witness_record(agent, o, Ordering::SeqCst, gc);
        // 5. If IsTypedArrayOutOfBounds(taRecord) is true, return +0𝔽.
        if match o {
            TypedArray::Int8Array(_) => is_typed_array_out_of_bounds::<i8>(agent, &ta_record, gc),
            TypedArray::Uint8Array(_) => is_typed_array_out_of_bounds::<u8>(agent, &ta_record, gc),
            TypedArray::Uint8ClampedArray(_) => {
                is_typed_array_out_of_bounds::<U8Clamped>(agent, &ta_record, gc)
            }
            TypedArray::Int16Array(_) => is_typed_array_out_of_bounds::<i16>(agent, &ta_record, gc),
            TypedArray::Uint16Array(_) => {
                is_typed_array_out_of_bounds::<u16>(agent, &ta_record, gc)
            }
            TypedArray::Int32Array(_) => is_typed_array_out_of_bounds::<i32>(agent, &ta_record, gc),
            TypedArray::Uint32Array(_) => {
                is_typed_array_out_of_bounds::<u32>(agent, &ta_record, gc)
            }
            TypedArray::BigInt64Array(_) => {
                is_typed_array_out_of_bounds::<i64>(agent, &ta_record, gc)
            }
            TypedArray::BigUint64Array(_) => {
                is_typed_array_out_of_bounds::<u64>(agent, &ta_record, gc)
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => {
                is_typed_array_out_of_bounds::<f16>(agent, &ta_record, gc)
            }
            TypedArray::Float32Array(_) => {
                is_typed_array_out_of_bounds::<f32>(agent, &ta_record, gc)
            }
            TypedArray::Float64Array(_) => {
                is_typed_array_out_of_bounds::<f64>(agent, &ta_record, gc)
            }
        } {
            return Ok(Value::pos_zero());
        }
        // 6. Let length be TypedArrayLength(taRecord).
        let length = match o {
            TypedArray::Int8Array(_) => typed_array_length::<i8>(agent, &ta_record, gc),
            TypedArray::Uint8Array(_) => typed_array_length::<u8>(agent, &ta_record, gc),
            TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<U8Clamped>(agent, &ta_record, gc)
            }
            TypedArray::Int16Array(_) => typed_array_length::<i16>(agent, &ta_record, gc),
            TypedArray::Uint16Array(_) => typed_array_length::<u16>(agent, &ta_record, gc),
            TypedArray::Int32Array(_) => typed_array_length::<i32>(agent, &ta_record, gc),
            TypedArray::Uint32Array(_) => typed_array_length::<u32>(agent, &ta_record, gc),
            TypedArray::BigInt64Array(_) => typed_array_length::<i64>(agent, &ta_record, gc),
            TypedArray::BigUint64Array(_) => typed_array_length::<u64>(agent, &ta_record, gc),
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_length::<f16>(agent, &ta_record, gc),
            TypedArray::Float32Array(_) => typed_array_length::<f32>(agent, &ta_record, gc),
            TypedArray::Float64Array(_) => typed_array_length::<f64>(agent, &ta_record, gc),
        } as i64;
        // 7. Return 𝔽(length).
        Ok(Value::try_from(length).unwrap())
    }

    fn map(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn reduce(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn reduce_right(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn reverse(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn set(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    fn slice(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!()
    }

    /// ### [23.2.3.28 get %TypedArray%.prototype.some](https://tc39.es/ecma262/multipage/indexed-collections.html#sec-%typedarray%.prototype.some)
    fn some(
        agent: &mut Agent,
        this_value: Value,
        arguments: ArgumentsList,
        mut gc: GcScope,
    ) -> JsResult<Value> {
        let callback = arguments.get(0).bind(gc.nogc());
        let this_arg = arguments.get(1).bind(gc.nogc());
        // 1. Let O be the this value.
        let o = this_value;
        // 2. Let taRecord be ? ValidateTypedArray(O, seq-cst).
        let ta_record = validate_typed_array(agent, o, Ordering::SeqCst, gc.nogc())?;
        let mut o = ta_record.object;
        // 3. Let len be TypedArrayLength(taRecord).
        let len = match o {
            TypedArray::Int8Array(_)
            | TypedArray::Uint8Array(_)
            | TypedArray::Uint8ClampedArray(_) => {
                typed_array_length::<u8>(agent, &ta_record, gc.nogc())
            }
            TypedArray::Int16Array(_) | TypedArray::Uint16Array(_) => {
                typed_array_length::<u16>(agent, &ta_record, gc.nogc())
            }
            #[cfg(feature = "proposal-float16array")]
            TypedArray::Float16Array(_) => typed_array_length::<f16>(agent, &ta_record, gc.nogc()),
            TypedArray::Int32Array(_)
            | TypedArray::Uint32Array(_)
            | TypedArray::Float32Array(_) => {
                typed_array_length::<u32>(agent, &ta_record, gc.nogc())
            }
            TypedArray::BigInt64Array(_)
            | TypedArray::BigUint64Array(_)
            | TypedArray::Float64Array(_) => {
                typed_array_length::<u64>(agent, &ta_record, gc.nogc())
            }
        };
        // 4. If IsCallable(callback) is false, throw a TypeError exception.
        let Some(callback) = is_callable(callback, gc.nogc()) else {
            return Err(agent.throw_exception_with_static_message(
                ExceptionType::TypeError,
                "Callback is not callable",
                gc.nogc(),
            ));
        };
        let callback = callback.scope(agent, gc.nogc());
        let scoped_o = o.scope(agent, gc.nogc());
        // 5. Let k be 0.
        let mut k = 0;
        // 6. Repeat, while k < len,
        while k < len {
            // a. Let Pk be ! ToString(𝔽(k)).
            let pk = PropertyKey::from(SmallInteger::from(k as u32));
            // b. Let kValue be ! Get(O, Pk).
            let k_value = unwrap_try(try_get(agent, o, pk, gc.nogc()));
            // c. Let testResult be ToBoolean(? Call(callback, thisArg, « kValue, 𝔽(k), O »)).
            let call = call_function(
                agent,
                callback.get(agent),
                this_arg,
                Some(ArgumentsList(&[
                    k_value,
                    Number::try_from(k).unwrap().into_value(),
                    o.into_value(),
                ])),
                gc.reborrow(),
            )?;
            let test_result = to_boolean(agent, call);
            // d. If testResult is true, return true.
            if test_result {
                return Ok(true.into());
            }
            // e. Set k to k + 1.
            o = scoped_o.get(agent).bind(gc.nogc());
            k += 1;
        }
        // 7. Return false.
        Ok(false.into())
    }

    fn sort(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn subarray(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn to_locale_string(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn to_reversed(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn to_sorted(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    fn to_spliced(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    /// ### [23.2.3.35 %TypedArray%.prototype.values ( )](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype-%symbol.tostringtag%)
    fn values(
        agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        gc: GcScope,
    ) -> JsResult<Value> {
        // 1. Let O be the this value.
        // 2. Perform ? ValidateTypedArray(O, seq-cst).
        let o = validate_typed_array(agent, this_value, Ordering::SeqCst, gc.nogc())?.object;
        // 3. Return CreateArrayIterator(O, value).
        Ok(
            ArrayIterator::from_object(agent, o.into_object(), CollectionIteratorKind::Value)
                .into_value(),
        )
    }

    fn with(
        _agent: &mut Agent,
        _this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        todo!();
    }

    /// ### [23.2.3.38 get %TypedArray%.prototype \[ %Symbol.toStringTag% \]](https://tc39.es/ecma262/#sec-get-%typedarray%.prototype-%symbol.tostringtag%)
    fn get_to_string_tag(
        _agent: &mut Agent,
        this_value: Value,
        _: ArgumentsList,
        _gc: GcScope,
    ) -> JsResult<Value> {
        // 1. Let O be the this value.
        if let Ok(o) = TypedArray::try_from(this_value) {
            // 4. Let name be O.[[TypedArrayName]].
            // 5. Assert: name is a String.
            // 6. Return name.
            match o {
                TypedArray::Int8Array(_) => Ok(BUILTIN_STRING_MEMORY.Int8Array.into()),
                TypedArray::Uint8Array(_) => Ok(BUILTIN_STRING_MEMORY.Uint8Array.into()),
                TypedArray::Uint8ClampedArray(_) => {
                    Ok(BUILTIN_STRING_MEMORY.Uint8ClampedArray.into())
                }
                TypedArray::Int16Array(_) => Ok(BUILTIN_STRING_MEMORY.Int16Array.into()),
                TypedArray::Uint16Array(_) => Ok(BUILTIN_STRING_MEMORY.Uint16Array.into()),
                TypedArray::Int32Array(_) => Ok(BUILTIN_STRING_MEMORY.Int32Array.into()),
                TypedArray::Uint32Array(_) => Ok(BUILTIN_STRING_MEMORY.Uint32Array.into()),
                TypedArray::BigInt64Array(_) => Ok(BUILTIN_STRING_MEMORY.BigInt64Array.into()),
                TypedArray::BigUint64Array(_) => Ok(BUILTIN_STRING_MEMORY.BigUint64Array.into()),
                #[cfg(feature = "proposal-float16array")]
                TypedArray::Float16Array(_) => Ok(BUILTIN_STRING_MEMORY.Float16Array.into()),
                TypedArray::Float32Array(_) => Ok(BUILTIN_STRING_MEMORY.Float32Array.into()),
                TypedArray::Float64Array(_) => Ok(BUILTIN_STRING_MEMORY.Float64Array.into()),
            }
        } else {
            // 2. If O is not an Object, return undefined.
            // 3. If O does not have a [[TypedArrayName]] internal slot, return undefined.
            Ok(Value::Undefined)
        }
    }

    pub(crate) fn create_intrinsic(agent: &mut Agent, realm: RealmIdentifier) {
        let intrinsics = agent.get_realm(realm).intrinsics();
        let object_prototype = intrinsics.object_prototype();
        let this = intrinsics.typed_array_prototype();
        let typed_array_constructor = intrinsics.typed_array();
        let typed_array_prototype_values = intrinsics.typed_array_prototype_values();
        let array_prototype_to_string = intrinsics.array_prototype_to_string();

        OrdinaryObjectBuilder::new_intrinsic_object(agent, realm, this)
            .with_property_capacity(38)
            .with_prototype(object_prototype)
            .with_builtin_function_property::<TypedArrayPrototypeAt>()
            .with_builtin_function_getter_property::<TypedArrayPrototypeGetBuffer>()
            .with_builtin_function_getter_property::<TypedArrayPrototypeGetByteLength>()
            .with_builtin_function_getter_property::<TypedArrayPrototypeGetByteOffset>()
            .with_constructor_property(typed_array_constructor)
            .with_builtin_function_property::<TypedArrayPrototypeCopyWithin>()
            .with_builtin_function_property::<TypedArrayPrototypeEntries>()
            .with_builtin_function_property::<TypedArrayPrototypeEvery>()
            .with_builtin_function_property::<TypedArrayPrototypeFill>()
            .with_builtin_function_property::<TypedArrayPrototypeFilter>()
            .with_builtin_function_property::<TypedArrayPrototypeFind>()
            .with_builtin_function_property::<TypedArrayPrototypeFindIndex>()
            .with_builtin_function_property::<TypedArrayPrototypeFindLast>()
            .with_builtin_function_property::<TypedArrayPrototypeFindLastIndex>()
            .with_builtin_function_property::<TypedArrayPrototypeForEach>()
            .with_builtin_function_property::<TypedArrayPrototypeIncludes>()
            .with_builtin_function_property::<TypedArrayPrototypeIndexOf>()
            .with_builtin_function_property::<TypedArrayPrototypeJoin>()
            .with_builtin_function_property::<TypedArrayPrototypeKeys>()
            .with_builtin_function_property::<TypedArrayPrototypeLastIndexOf>()
            .with_builtin_function_getter_property::<TypedArrayPrototypeGetLength>()
            .with_builtin_function_property::<TypedArrayPrototypeMap>()
            .with_builtin_function_property::<TypedArrayPrototypeReduce>()
            .with_builtin_function_property::<TypedArrayPrototypeReduceRight>()
            .with_builtin_function_property::<TypedArrayPrototypeReverse>()
            .with_builtin_function_property::<TypedArrayPrototypeSet>()
            .with_builtin_function_property::<TypedArrayPrototypeSlice>()
            .with_builtin_function_property::<TypedArrayPrototypeSome>()
            .with_builtin_function_property::<TypedArrayPrototypeSort>()
            .with_builtin_function_property::<TypedArrayPrototypeSubarray>()
            .with_builtin_function_property::<TypedArrayPrototypeToLocaleString>()
            .with_builtin_function_property::<TypedArrayPrototypeToReversed>()
            .with_builtin_function_property::<TypedArrayPrototypeToSorted>()
            .with_property(|builder| {
                builder
                    .with_key(BUILTIN_STRING_MEMORY.toString.into())
                    .with_value(array_prototype_to_string.into_value())
                    .with_enumerable(false)
                    .with_configurable(true)
                    .build()
            })
            .with_builtin_intrinsic_function_property::<TypedArrayPrototypeValues>()
            .with_builtin_function_property::<TypedArrayPrototypeWith>()
            .with_builtin_function_getter_property::<TypedArrayPrototypeGetToStringTag>()
            .with_property(|builder| {
                builder
                    .with_key(WellKnownSymbolIndexes::Iterator.into())
                    .with_value(typed_array_prototype_values.into_value())
                    .with_enumerable(TypedArrayPrototypeValues::ENUMERABLE)
                    .with_configurable(TypedArrayPrototypeValues::CONFIGURABLE)
                    .build()
            })
            .build();
    }
}

#[inline]
pub(crate) fn require_internal_slot_typed_array<'a>(
    agent: &mut Agent,
    o: Value,
    gc: NoGcScope<'a, '_>,
) -> JsResult<TypedArray<'a>> {
    // 1. Perform ? RequireInternalSlot(O, [[TypedArrayName]]).
    TypedArray::try_from(o).map_err(|_| {
        agent.throw_exception_with_static_message(
            crate::ecmascript::execution::agent::ExceptionType::TypeError,
            "Expected this to be TypedArray",
            gc,
        )
    })
}
