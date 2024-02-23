/* date = December 3rd 2023 6:38 pm */

#ifndef CHECK_H
#define CHECK_H

#include "parser.h"
#include "base/ds.h"
#include "base/mem.h"
#include "base/str.h"

//~ Types

typedef enum TypeKind {
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
} TypeKind;

typedef struct ValueType ValueType;
typedef u64 TypeIndex;

typedef struct TypeInt {
  u32 size;
  b8 is_signed;
} TypeInt;

typedef struct TypeFloat {
  u32 size;
} TypeFloat;

typedef struct TypeFunc {
  TypeIndex ret_t;
  u32 arity;
  TypeIndex* arg_ts;
} TypeFunc;

typedef struct TypePointer {
  TypeIndex sub_t;
} TypePointer;

typedef struct TypeArray {
  TypeIndex sub_t;
  u64 count;
} TypeArray;

typedef struct TypeCompound {
  string name;
  TypeIndex* member_ts;
  Token_list member_names;
  u64* member_offsets;
  u64 count;
} TypeCompound;

struct ValueType {
  TypeKind type;
  u64 size;
  
  union {
    TypeInt int_t;
    TypeFloat float_t;
    TypeFunc func_t;
    TypePointer ptr_t;
    TypeArray array_t;
    TypeCompound compound_t;
  };
};

typedef ValueType* ValueTypeRef;
DArray_Prototype(ValueTypeRef);

typedef struct ValueTypeBucket ValueTypeBucket;
struct ValueTypeBucket {
  ValueType* type;
  ASTNode* key;
  
  ValueTypeBucket* hash_next;
  ValueTypeBucket* hash_prev;
};


typedef struct Symbol {
  Token ident;
  ASTNode* node;
  TypeIndex type;
  u32 scope;
  b8 is_constant;
  ConstantValue constant_val;
} Symbol;
DArray_Prototype(Symbol);


typedef u32 ScopeResetPoint;

// Required members: 'scope u32' and 'symbols darray(T)'
#define scope_push(o)   ((o)->scope++, (o)->symbols.len)
#define scope_pop(o, p) ((o)->scope--, (o)->symbols.len = p)


typedef enum CheckingWorkType {
  Work_Decl,
  Work_SimpleCheck,
} CheckingWorkType;

typedef struct CheckingWork {
  CheckingWorkType type;
  
  ASTNode* ref;
  TypeIndex* to_update;
} CheckingWork;

Queue_Prototype(CheckingWork);

//~ Checker

typedef struct Checker {
  ASTNode* tree;
  M_Pool   allocator;
  M_Arena  arena;
  string   filename;
  u32      scope;
  b8       errored;
  b8       cycles_exist;
  
  dqueue(CheckingWork) worklist;
  darray(ASTNodeRef_array) cycle_checker;
  
  darray(ValueTypeRef) type_cache;
  darray(Symbol) symbols;
} Checker;

void Checker_Init(Checker* checker);
void Checker_Check(Checker* checker, ASTNode* tree);
void Checker_Free(Checker* checker);

string Debug_GetTypeString(Checker* c, TypeIndex idx);

#endif //CHECK_H
