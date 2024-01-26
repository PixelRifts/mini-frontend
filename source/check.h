/* date = December 3rd 2023 6:38 pm */

#ifndef CHECK_H
#define CHECK_H

#include "parser.h"
#include "base/ds.h"
#include "base/mem.h"
#include "base/str.h"

//~ Types

typedef u32 TypeKind;
enum {
  TK_None,
  TK_Int,
  TK_Float,
  TK_Func,
  TK_Type,
  TK_Void,
  TK_Bool,
  TK_Pointer,
  TK_Array,
  TK_Struct,
  TK_Union,
  
  TK_MAX,
};

typedef struct ValueType ValueType;

typedef struct TypeInt {
  u32 size;
  b8 is_signed;
} TypeInt;

typedef struct TypeFloat {
  u32 size;
} TypeFloat;

typedef struct TypeFunc {
  ValueType* ret_t;
  u32 arity;
  ValueType** arg_ts;
} TypeFunc;

typedef struct TypePointer {
  ValueType* sub_t;
} TypePointer;

typedef struct TypeArray {
  ValueType* sub_t;
  u64 count;
} TypeArray;

typedef struct TypeCompound {
  ValueType** member_ts;
  Token_list member_names;
  u64 count;
} TypeCompound;

struct ValueType {
  TypeKind type;
  
  union {
    TypeInt int_t;
    TypeFloat float_t;
    TypeFunc func_t;
    TypePointer ptr_t;
    TypeArray array_t;
    TypeCompound compound_t;
  };
};

typedef struct ValueTypeBucket ValueTypeBucket;
struct ValueTypeBucket {
  ValueType* type;
  ASTNode* key;
  
  ValueTypeBucket* hash_next;
  ValueTypeBucket* hash_prev;
};

typedef ASTNode* ASTFuncRef;
typedef ValueType* ValueTypeRef;
StableTable_Prototype(ASTFuncRef, ValueTypeBucket);

//~ Checker


typedef enum ModdedTypeKind {
  MTK_None,
  MTK_Pointer,
  MTK_Array,
} ModdedTypeKind;
typedef struct ModdedTypeKey {
  ModdedTypeKind type;
  ValueType* sub;
  union {
    u64 count;
  };
} ModdedTypeKey;
typedef struct ModdedValueTypeBucket ModdedValueTypeBucket;
struct ModdedValueTypeBucket {
  ValueType* type;
  ModdedTypeKey key;
  
  ModdedValueTypeBucket* hash_next;
  ModdedValueTypeBucket* hash_prev;
};
StableTable_Prototype(ModdedTypeKey, ModdedValueTypeBucket);


typedef ASTNode* ASTCompoundTypeRef;
StableTable_Prototype(ASTCompoundTypeRef, ValueTypeBucket);


typedef struct StringArrayBucket StringArrayBucket;
struct StringArrayBucket {
  ASTNode* key;
  StringArrayBucket* hash_next;
  StringArrayBucket* hash_prev;
  
  string_array strings;
};
StableTable_Prototype(ASTNodeRef, StringArrayBucket);

typedef struct Symbol {
  Token ident;
  ValueType* type;
  u32 scope;
  b8 is_constant;
  ConstantValue constant_val;
} Symbol;
DArray_Prototype(Symbol);

typedef struct Checker {
  ASTNode* tree;
  M_Pool   allocator;
  M_Arena  arena;
  string   filename;
  u32      scope;
  b8       errored;
  b8       ident_dnf;
  b8       ident_guarantee;
  ASTNode* curr_stmt;
  
  stable_table(ASTFuncRef, ValueTypeBucket) func_type_cache;
  stable_table(ModdedTypeKey, ModdedValueTypeBucket) modded_type_cache;
  stable_table(ASTCompoundTypeRef, ValueTypeBucket) compound_type_cache;
  darray(Symbol) symbols;
  
  // TODO(voxel): Switch to darray, it's just going to be obviously better
  //              Why on earth did I think a stable table would be good here
  stable_table(ASTNodeRef, StringArrayBucket) pending_nodes;
} Checker;

void Checker_Init(Checker* checker);
void Checker_Check(Checker* checker, ASTNode* tree);
void Checker_Free(Checker* checker);

string Debug_GetTypeString(M_Arena* arena, ValueType* type);

#endif //CHECK_H
