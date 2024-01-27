#include "check.h"
#include "base/log.h"

//~ Preproc Params

// #define PRINT_ON_SYMBOL_REGISTER

//~

#define CheckerError(c, t, f, ...)\
Statement(\
if (!c->errored) printf("%.*s:%d:%d - Check Error - " f,\
str_expand(c->filename), t.line, t.col,\
##__VA_ARGS__);\
c->errored = true;\
)

enum {
  Type_Index_None,
  
  Type_Index_I32,
  Type_Index_I64,
  Type_Index_U32,
  Type_Index_U64,
  Type_Index_F32,
  Type_Index_F64,
  Type_Index_Type,
  Type_Index_Void,
  Type_Index_Bool,
  
  Type_Index_Count,
};
static ValueType* type_refs[Type_Index_Count] = {0};

//~

#define FNV_OFFSET_BASIS 14695981039346656037ull
#define FNV_PRIME 1099511628211llu
M_Arena* global_arena_t;

#define printtype(t) Statement(\
string v = Debug_GetTypeString(global_arena_t, t);\
printf("%.*s\n", str_expand(v));\
)

static b8 func_node_is_null(ASTNode* node) { return node == nullptr; }
static b8 func_nodes_eq(ASTNode* a, ASTNode* b) {
  ASTNode* a_return_type = a->type == NT_Expr_Func
    ? a->func.return_type : a->func_type.return_type;
  ASTNode* a_curr = a->type == NT_Expr_Func
    ? a->func.arg_types : a->func_type.arg_types;
  u32 a_arity = a->type == NT_Expr_Func
    ? a->func.arity : a->func_type.arity;
  ASTNode* b_return_type = b->type == NT_Expr_Func
    ? b->func.return_type : b->func_type.return_type;
  ASTNode* b_curr = b->type == NT_Expr_Func
    ? b->func.arg_types : b->func_type.arg_types;
  u32 b_arity = b->type == NT_Expr_Func
    ? b->func.arity : b->func_type.arity;
  
  if (a_arity != b_arity) return false;
  if (a_return_type->constant_val.type_lit != b_return_type->constant_val.type_lit)
    return false;
  while (a_arity--) {
    if (a_curr->constant_val.type_lit != b_curr->constant_val.type_lit) return false;
    a_curr = a_curr->next;
    b_curr = b_curr->next;
  }
  return true;
}
static u64 hash_func(ASTNode* node) {
  u64 hash = FNV_OFFSET_BASIS;
  if (node->type == NT_Expr_Func) {
    if (node->func.return_type) {
      hash ^= (u64) node->func.return_type->constant_val.type_lit;
      hash *= FNV_PRIME;
    } else {
      hash ^= (u64) type_refs[Type_Index_Void];
      hash *= FNV_PRIME;
    }
    
    ASTNode* curr = node->func.arg_types;
    while (curr) {
      hash ^= (u64) curr->constant_val.type_lit;
      hash *= FNV_PRIME;
      curr = curr->next;
    }
  } else {
    if (node->func_type.return_type) {
      hash ^= (u64) node->func_type.return_type->constant_val.type_lit;
      hash *= FNV_PRIME;
    } else {
      hash ^= (u64) type_refs[Type_Index_Void];
      hash *= FNV_PRIME;
    }
    
    ASTNode* curr = node->func_type.arg_types;
    while (curr) {
      hash ^= (u64) curr->constant_val.type_lit;
      hash *= FNV_PRIME;
      curr = curr->next;
    }
  }
  return hash;
}

StableTable_Impl(ASTFuncRef, ValueTypeBucket, func_node_is_null, func_nodes_eq,
                 hash_func);

static b8 modded_type_key_is_null(ModdedTypeKey key) {
  return memcmp(&key, &(ModdedTypeKey) {0}, sizeof(ModdedTypeKey));
}
static b8 modded_type_keys_eq(ModdedTypeKey a, ModdedTypeKey b) {
  if (a.type != b.type) return false;
  if (a.sub != b.sub) return false;
  
  switch (a.type) {
    case MTK_None: return true;
    case MTK_Pointer: return true;
    case MTK_Array: return a.count == b.count;
  }
  
  return false;
}
static u64 modded_type_key_hash(ModdedTypeKey key) {
  u64 hash = FNV_OFFSET_BASIS;
  hash ^= (u64) key.type;
  hash *= FNV_PRIME;
  hash ^= (u64) key.sub;
  hash *= FNV_PRIME;
  
  switch (key.type) {
    case MTK_None: break;
    case MTK_Pointer: break;
    case MTK_Array: {
      hash ^= key.count;
      hash *= FNV_PRIME;
    } break;
  }
  
  return hash;
}
StableTable_Impl(ModdedTypeKey, ModdedValueTypeBucket, modded_type_key_is_null, modded_type_keys_eq, modded_type_key_hash);


static b8 compound_type_node_is_null(ASTNode* node) { return node == nullptr; }
static b8 compound_type_nodes_eq(ASTNode* a, ASTNode* b) {
  if (a->type != b->type) return false;
  if (a->compound_type.member_count != b->compound_type.member_count) return false;
  ASTNode* a_curr_type = a->compound_type.member_types;
  ASTNode* b_curr_type = b->compound_type.member_types;
  for (u64 i = 0; i < a->compound_type.member_count; i++) {
    if (a_curr_type != b_curr_type) return false;
    a_curr_type = a_curr_type->next;
    b_curr_type = b_curr_type->next;
  }
  return true;
}
static u64 hash_compound_type_node(ASTNode* key) {
  u64 hash = FNV_OFFSET_BASIS;
  hash ^= (u64) key->type;
  hash *= FNV_PRIME;
  hash ^= key->compound_type.member_count;
  hash *= FNV_PRIME;
  ASTNode* curr_type = key->compound_type.member_types;
  while (curr_type) {
    hash ^= (u64) curr_type->constant_val.type_lit;
    hash *= FNV_PRIME;
    curr_type = curr_type->next;
  }
  return hash;
}
StableTable_Impl(ASTCompoundTypeRef, ValueTypeBucket, compound_type_node_is_null, compound_type_nodes_eq, hash_compound_type_node);

static b8  ast_node_is_null(ASTNode* node) { return node == nullptr; }
static b8  ast_nodes_eq(ASTNode* a, ASTNode* b) { return a == b; }
static u64 hash_node(ASTNode* node) { return ((u64)node) * FNV_PRIME; }
StableTable_Impl(ASTNodeRef, StringArrayBucket, ast_node_is_null, ast_nodes_eq,
                 hash_node);

DArray_Impl(Symbol);

static b8 IdentifierLookup(Checker* checker, string id, u32* idx) {
  for (i32 i = checker->symbols.len-1; i >= 0; i--) {
    if (str_eq(checker->symbols.elems[i].ident.lexeme, id)) {
      *idx = i;
      return true;
    }
  }
  return false;
}

#define CheckAbsolute(a, b) ((a)==(b))
//static b8 CheckAbsolute(ValueType* a, ValueType* b) {
//if (a == b) return true;
//return false;
//}



typedef u32 ScopeResetPoint;
ScopeResetPoint scope_push(Checker* checker) {
  checker->scope += 1;
  return checker->symbols.len;
}
void scope_pop(Checker* checker, ScopeResetPoint point) {
  checker->scope -= 1;
  checker->symbols.len = point;
}


static ValueType* reduce_type(ValueType* type) {
  if (type->type == TK_Pointer) {
    return type->ptr_t.sub_t;
  } else if (type->type == TK_Array) {
    return type->array_t.sub_t;
  } else {
    string ty = Debug_GetTypeString(global_arena_t, type);
    LogError("Internal Compiler Error: Failed to reduce type '%.*s'", str_expand(ty));
  }
  return type_refs[Type_Index_None];
}


static ValueType* push_pointer_type(Checker* checker, ValueType* sub) {
  ModdedTypeKey key = (ModdedTypeKey) {
    .type  = MTK_Pointer,
    .sub   = sub,
  };
  
  ModdedValueTypeBucket* val;
  if (!stable_table_get(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache, key, &val)) {
    ModdedValueTypeBucket bucket = {0};
    bucket.type = pool_alloc(&checker->allocator);
    bucket.type->type = TK_Pointer;
    bucket.type->ptr_t.sub_t = sub;
    stable_table_set(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache, key, bucket);
    return bucket.type;
  }
  
  return val->type;
}

static ValueType* push_array_type(Checker* checker, ValueType* sub, u64 count) {
  ModdedTypeKey key = (ModdedTypeKey) {
    .type  = MTK_Array,
    .sub   = sub,
    .count = count,
  };
  
  ModdedValueTypeBucket* val;
  if (!stable_table_get(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache, key, &val)) {
    ModdedValueTypeBucket bucket = {0};
    bucket.type = pool_alloc(&checker->allocator);
    bucket.type->type = TK_Array;
    bucket.type->array_t.sub_t = sub;
    bucket.type->array_t.count = count;
    stable_table_set(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache, key, bucket);
    
    return bucket.type;
  }
  
  return val->type;
}

static b8 is_lvalue(ASTNode* node) {
  return node->type == NT_Expr_Deref ||
    node->type == NT_Expr_Index ||
    node->type == NT_Expr_Access ||
    node->type == NT_Expr_Ident;
}

static b8 is_castable(ValueType* a, ValueType* b) {
  switch (b->type) {
    case TK_Int:
    case TK_Float: {
      return a->type == TK_Int || a->type == TK_Float;
    } break;
    
    case TK_Func: {
      if (a->type != TK_Func) return false;
      // Do more here maybe
      return true;
    } break;
    
    case TK_Bool: {
      return a->type == TK_Bool;
    } break;
    
    case TK_Pointer: {
      return a->type == TK_Pointer;
    } break;
    
    case TK_Array: {
      return false;
    } break;
    
    case TK_Struct:
    case TK_Union: {
      if (a->type != b->type) return false;
      if (a->compound_t.count != b->compound_t.count) return false;
      for (u64 i = 0; i < a->compound_t.count; i++) {
        if (!CheckAbsolute(a->compound_t.member_ts[i], b->compound_t.member_ts[i]))
          return false;
      }
      return true;
    } break;
  }
  
  return false;
}

//~ Helpers

static void Checker_CheckNode(Checker* checker, ASTNode* node);
static void Checker_CheckOuter(Checker* checker, ASTNode* node);

#define CheckerReturnIfIdentDNF(c) if (c->ident_dnf && !c->scope) return;
#define CheckerAssertion(c, cond) if (!c->ident_dnf && (cond))
#define CheckerSetCurrentStatement(c, n) Statement(\
c->curr_stmt = n;\
c->ident_dnf = false;\
)

static void Checker_CheckInner(Checker* checker, ASTNode* node) {
  if (!node) return;
  
  switch (node->type) {
    case NT_Expr_Func: {
      Checker_CheckInner(checker, node->func.return_type);
      
      ScopeResetPoint sp = scope_push(checker);
      
      ASTNode* curr = node->func.arg_types;
      Token_node* curr_name = node->func.arg_names.first;
      
      while (curr) {
        Checker_CheckInner(checker, curr);
        
        Symbol k = (Symbol) {
          .ident = curr_name->token,
          .scope = checker->scope,
          .type = curr->constant_val.type_lit,
          .is_constant = node->decl.is_constant,
        };
        darray_add(Symbol, &checker->symbols, k);
        
        curr = curr->next;
        curr_name = curr_name->next;
      }
      
      Checker_CheckNode(checker, node->func.body);
      
      scope_pop(checker, sp);
    } break;
    
    case NT_Stmt_Block: {
      ASTNode* curr = node->block;
      
      ScopeResetPoint sp = scope_push(checker);
      while (curr) {
        Checker_CheckNode(checker, curr);
        curr = curr->next;
      }
      scope_pop(checker, sp);
    } break;
    
    case NT_Stmt_While: {
      Checker_CheckInner(checker, node->while_loop.condition);
      ASTNode* curr = node->while_loop.body;
      
      ScopeResetPoint sp = scope_push(checker);
      while (curr) {
        Checker_CheckNode(checker, curr);
        curr = curr->next;
      }
      scope_pop(checker, sp);
    } break;
    
    case NT_Stmt_If: {
      Checker_CheckInner(checker, node->if_stmt.condition);
      
      ScopeResetPoint sp = scope_push(checker);
      Checker_CheckNode(checker, node->if_stmt.then_body);
      scope_pop(checker, sp);
      
      if (node->if_stmt.else_body) {
        ScopeResetPoint sp = scope_push(checker);
        Checker_CheckNode(checker, node->if_stmt.else_body);
        scope_pop(checker, sp);
      }
    } break;
    
    case NT_Error:
    case NT_Expr_IntLit:
    case NT_Expr_FloatLit: {
    } break;
    
    case NT_Expr_Add:
    case NT_Expr_Sub:
    case NT_Expr_Mul:
    case NT_Expr_Div: {
      Checker_CheckInner(checker, node->binary_op.left);
      Checker_CheckInner(checker, node->binary_op.right);
    } break;
    
    case NT_Expr_Mod: {
      Checker_CheckInner(checker, node->binary_op.left);
      Checker_CheckInner(checker, node->binary_op.right);
    } break;
    
    case NT_Expr_Identity:
    case NT_Expr_Negate: {
      Checker_CheckInner(checker, node->unary_op.operand);
    } break;
    
    case NT_Expr_Eq:
    case NT_Expr_Neq:
    case NT_Expr_Less:
    case NT_Expr_Greater:
    case NT_Expr_LessEq:
    case NT_Expr_GreaterEq: {
      Checker_CheckInner(checker, node->binary_op.left);
      Checker_CheckInner(checker, node->binary_op.right);
    } break;
    
    case NT_Expr_Call: {
      Checker_CheckInner(checker, node->call.called);
      ASTNode* curr = node->call.args;
      while (curr) {
        Checker_CheckInner(checker, curr);
        curr = curr->next;
      }
    } break;
    
    case NT_Expr_Ident: {
    } break;
    
    case NT_Expr_Index: {
      Checker_CheckInner(checker, node->index.left);
      Checker_CheckInner(checker, node->index.idx);
    } break;
    
    case NT_Expr_Deref: {
      Checker_CheckInner(checker, node->deref);
    } break;
    
    case NT_Expr_Addr: {
      Checker_CheckInner(checker, node->addr);
    } break;
    
    case NT_Expr_Not: {
      Checker_CheckInner(checker, node->unary_op.operand);
    } break;
    
    case NT_Expr_Cast: {
      Checker_CheckInner(checker, node->cast.casted);
      Checker_CheckInner(checker, node->cast.type);
    } break;
    
    case NT_Expr_Access: {
      
    } break;
    
    case NT_Type_Integer:
    case NT_Type_Float:
    case NT_Type_Void: {
    } break;
    
    case NT_Type_Func: {
      Checker_CheckInner(checker, node->func_type.return_type);
      ASTNode* curr = node->func_type.arg_types;
      while (curr) {
        Checker_CheckInner(checker, curr);
        curr = curr->next;
      }
    } break;
    
    case NT_Type_Pointer: {
      Checker_CheckInner(checker, node->pointer_type.sub);
    } break;
    
    case NT_Type_Array: {
      Checker_CheckInner(checker, node->array_type.sub);
      Checker_CheckInner(checker, node->array_type.count);
    } break;
    
    case NT_Type_Struct:
    case NT_Type_Union: {
      ASTNode* curr = node->compound_type.member_types;
      while (curr) {
        Checker_CheckInner(checker, curr);
        curr = curr->next;
      }
    } break;
    
    case NT_Stmt_Assign: {
      Checker_CheckInner(checker, node->binary_op.left);
      Checker_CheckInner(checker, node->binary_op.right);
    } break;
    
    case NT_Stmt_Expr: {
      Checker_CheckInner(checker, node->expr_stmt);
    } break;
    
    case NT_Stmt_Return: {
      Checker_CheckInner(checker, node->return_stmt);
    } break;
    
    case NT_Decl: {
      Checker_CheckInner(checker, node->decl.type);
      Checker_CheckInner(checker, node->decl.val);
    } break;
    
    default: { } break;
  }
}

static void Checker_CheckOuter(Checker* checker, ASTNode* node) {
  if (!node) return;
  
  switch (node->type) {
    case NT_Error: node->expr_type = type_refs[Type_Index_None]; break;
    case NT_Expr_IntLit: node->expr_type = type_refs[Type_Index_I32]; break;
    case NT_Expr_FloatLit: node->expr_type = type_refs[Type_Index_F32]; break;
    
    case NT_Expr_Add:
    case NT_Expr_Sub:
    case NT_Expr_Mul:
    case NT_Expr_Div: {
      Checker_CheckOuter(checker, node->binary_op.left);
      Checker_CheckOuter(checker, node->binary_op.right);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->binary_op.left->expr_type, node->binary_op.right->expr_type)) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        string right = Debug_GetTypeString(&checker->arena, node->binary_op.right->expr_type);
        CheckerError(checker, node->marker, "The LHS and RHS for the binary operator should have the same types, but we got %.*s and %.*s instead\n",
                     str_expand(left), str_expand(right));
      }
      
      node->expr_type = node->binary_op.left->expr_type;
    } break;
    
    case NT_Expr_Mod: {
      Checker_CheckOuter(checker, node->binary_op.left);
      Checker_CheckOuter(checker, node->binary_op.right);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->binary_op.left->expr_type, node->binary_op.right->expr_type)) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        string right = Debug_GetTypeString(&checker->arena, node->binary_op.right->expr_type);
        CheckerError(checker, node->marker, "The LHS and RHS for the binary operator should have the same types, but we got %.*s and %.*s instead\n",
                     str_expand(left), str_expand(right));
      }
      
      CheckerAssertion(checker, CheckAbsolute(node->binary_op.left->expr_type, type_refs[Type_Index_F32])) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        CheckerError(checker, node->marker, "The type %.*s should not be a float",
                     str_expand(left));
      }
      
      CheckerAssertion(checker, CheckAbsolute(node->binary_op.left->expr_type, type_refs[Type_Index_F64])) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        CheckerError(checker, node->marker, "The type %.*s should not be a float",
                     str_expand(left));
      }
      
      node->expr_type = node->binary_op.left->expr_type;
    } break;
    
    case NT_Expr_Identity:
    case NT_Expr_Negate: {
      Checker_CheckOuter(checker, node->unary_op.operand);
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = node->unary_op.operand->expr_type;
    } break;
    
    case NT_Expr_Not: {
      Checker_CheckOuter(checker, node->unary_op.operand);
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = type_refs[Type_Index_Bool];
    } break;
    
    case NT_Expr_Eq:
    case NT_Expr_Neq:
    case NT_Expr_Less:
    case NT_Expr_Greater:
    case NT_Expr_LessEq:
    case NT_Expr_GreaterEq: {
      Checker_CheckOuter(checker, node->binary_op.left);
      Checker_CheckOuter(checker, node->binary_op.right);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->binary_op.left->expr_type, node->binary_op.right->expr_type)) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        string right = Debug_GetTypeString(&checker->arena, node->binary_op.right->expr_type);
        CheckerError(checker, node->marker, "The LHS and RHS for the binary operator should have the same types, but we got %.*s and %.*s instead\n",
                     str_expand(left), str_expand(right));
      }
      node->expr_type = type_refs[Type_Index_Bool];
    } break;
    
    case NT_Expr_Func: {
      Checker_CheckOuter(checker, node->func.return_type);
      
      ASTNode* curr = node->func.arg_types;
      
      while (curr) {
        Checker_CheckOuter(checker, curr);
        CheckerAssertion(checker, !CheckAbsolute(curr->expr_type, type_refs[Type_Index_Type])) {
          string typ = Debug_GetTypeString(&checker->arena, curr->expr_type);
          CheckerError(checker, curr->marker, "Required a type for the parameter but got a '%.*s' instead\n",
                       str_expand(typ));
        }
        
        curr = curr->next;
      }
      
      CheckerReturnIfIdentDNF(checker);
      
      ValueTypeBucket* ty = {0};
      if (stable_table_get(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache,
                           node, &ty))  {
        node->expr_type = ty->type;
        return;
      }
      
      
      ValueTypeBucket bucket = {0};
      bucket.type = pool_alloc(&checker->allocator);
      bucket.type->type = TK_Func;
      bucket.type->func_t.ret_t = node->func.return_type->constant_val.type_lit;
      bucket.type->func_t.arg_ts =
        arena_alloc(&checker->arena, sizeof(ValueType*) * node->func.arity);
      bucket.type->func_t.arity = node->func.arity;
      
      curr = node->func.arg_types;
      for (int i = 0; i < node->func.arity; i++) {
        bucket.type->func_t.arg_ts[i] = curr->constant_val.type_lit;
        curr = curr->next;
      }
      
      stable_table_set(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache,
                       node, bucket);
      node->expr_type = bucket.type;
      
    } break;
    
    case NT_Expr_Call: {
      Checker_CheckOuter(checker, node->call.called);
      ASTNode* curr = node->call.args;
      while (curr) {
        Checker_CheckOuter(checker, curr);
        curr = curr->next;
      }
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, node->call.called->expr_type->type != TK_Func) {
        string called_fn_type = Debug_GetTypeString(&checker->arena, node->call.called->expr_type);
        CheckerError(checker, node->marker, "Called expression is not a function, it is a %.*s\n",
                     str_expand(called_fn_type));
      }
      
      CheckerAssertion(checker, node->call.called->expr_type->func_t.arity != node->call.arity) {
        CheckerError(checker, node->marker, "Number of arguments required (%d) for the function and the number of arguments you provided (%d) are not equal\n",
                     node->call.called->expr_type->func_t.arity,
                     node->call.arity);
      }
      curr = node->call.args;
      for (int i = 0; i < node->call.called->expr_type->func_t.arity; i++) {
        CheckerAssertion(checker, !CheckAbsolute(node->call.called->expr_type->func_t.arg_ts[i], curr->expr_type)) {
          string required_arg_type = Debug_GetTypeString(&checker->arena, node->call.called->expr_type->func_t.arg_ts[i]);
          string actual_arg_type = Debug_GetTypeString(&checker->arena, curr->expr_type);
          CheckerError(checker, node->marker, "Argument %d of the function call should have type %.*s but we got %.*s\n", i,
                       str_expand(required_arg_type),
                       str_expand(actual_arg_type));
        }
        curr = curr->next;
      }
      
      node->expr_type = node->call.called->expr_type->func_t.ret_t;
    } break;
    
    case NT_Expr_Ident: {
      if (node->expr_type == type_refs[Type_Index_None] && !checker->ident_guarantee)
        break;
      
      u32 idx;
      if (IdentifierLookup(checker, node->ident.lexeme, &idx)) {
        node->expr_type = checker->symbols.elems[idx].type;
        node->is_constant = checker->symbols.elems[idx].is_constant;
        node->constant_val = checker->symbols.elems[idx].constant_val;
        break;
      }
      
      if (checker->scope) {
        CheckerError(checker, node->marker, "Unresolved Identifier %.*s\n",
                     str_expand(node->ident.lexeme));
      } else {
        StringArrayBucket* addend = nullptr;
        if (stable_table_get(ASTNodeRef, StringArrayBucket, &checker->pending_nodes,
                             checker->curr_stmt, &addend)) {
          darray_add(string, &addend->strings, node->ident.lexeme);
        } else {
          StringArrayBucket da = {0};
          darray_add(string, &da.strings, node->ident.lexeme);
          stable_table_set(ASTNodeRef, StringArrayBucket, &checker->pending_nodes,
                           checker->curr_stmt, da);
        }
        checker->ident_dnf = true;
      }
      
      node->expr_type = type_refs[Type_Index_None];
      node->is_constant = false;
    } break;
    
    case NT_Expr_Index: {
      Checker_CheckOuter(checker, node->index.left);
      Checker_CheckOuter(checker, node->index.idx);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, node->index.left->expr_type->type != TK_Array &&
                       node->index.left->expr_type->type != TK_Pointer) {
        string ty = Debug_GetTypeString(&checker->arena, node->index.left->expr_type);
        CheckerError(checker, node->marker, "Only a pointer or array type can be indexed, but we got a '%.*s'\n", str_expand(ty));
      }
      
      CheckerAssertion(checker, node->index.idx->expr_type->type != TK_Int) {
        string ty = Debug_GetTypeString(&checker->arena, node->index.idx->expr_type);
        CheckerError(checker, node->marker, "Only integer indexes are allowed but we got a '%.*s'\n", str_expand(ty));
      }
      
      node->expr_type = reduce_type(node->index.left->expr_type);
    } break;
    
    case NT_Expr_Deref: {
      Checker_CheckOuter(checker, node->deref);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, node->deref->expr_type->type != TK_Pointer) {
        string ty = Debug_GetTypeString(&checker->arena, node->deref->expr_type);
        CheckerError(checker, node->marker, "Only a pointer can be dereferenced but we got a '%.*s'\n", str_expand(ty));
      }
      
      node->expr_type = reduce_type(node->deref->expr_type);
    } break;
    
    case NT_Expr_Addr: {
      Checker_CheckOuter(checker, node->addr);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !is_lvalue(node->addr)) {
        CheckerError(checker, node->marker, "You can only take the address of an addressable expression, but the given expression is not addressable\n");
      }
      
      node->expr_type = push_pointer_type(checker, node->addr->expr_type);
    } break;
    
    case NT_Expr_Cast: {
      Checker_CheckOuter(checker, node->cast.casted);
      Checker_CheckOuter(checker, node->cast.type);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !node->cast.type->is_constant || node->cast.type->constant_val.type != CVT_Type) {
        string t = Debug_GetTypeString(&checker->arena, node->cast.type->expr_type);
        CheckerError(checker, node->marker, "The expression to cast to can only be a type but we got a '%.*s'\n", str_expand(t));
      }
      
      CheckerAssertion(checker,
                       !is_castable(node->cast.casted->expr_type,
                                    node->cast.type->constant_val.type_lit)) {
        string t1 =
          Debug_GetTypeString(&checker->arena, node->cast.casted->expr_type);
        string t2 = Debug_GetTypeString(&checker->arena,
                                        node->cast.type->constant_val.type_lit);
        CheckerError(checker, node->marker, "'%.*s' cannot be casted to '%.*s'",
                     str_expand(t1), str_expand(t2));
      }
      
      node->expr_type = node->cast.type->constant_val.type_lit;
    } break;
    
    case NT_Expr_Access: {
      Checker_CheckOuter(checker, node->access.left);
      
      CheckerReturnIfIdentDNF(checker);
      
      ValueType* left_base_t = node->access.left->expr_type;
      ValueType* accessed_type = nullptr;
      if (node->access.deref) {
        b8 failed = false;
        CheckerAssertion(checker, left_base_t->type != TK_Pointer) failed = true;
        if (!failed) {
          CheckerAssertion(checker, !(left_base_t->ptr_t.sub_t->type == TK_Struct ||
                                      left_base_t->ptr_t.sub_t->type == TK_Union)) {
            failed = true;
          }
        }
        if (failed) {
          string t = Debug_GetTypeString(&checker->arena, left_base_t);
          CheckerError(checker, node->marker, "The left expression is not a pointer to a struct or union type, it is a '%.*s'", str_expand(t));
        } else accessed_type = left_base_t->ptr_t.sub_t;
      } else {
        CheckerAssertion(checker, !(left_base_t->type == TK_Struct || 
                                    left_base_t->type == TK_Union)) {
          string t = Debug_GetTypeString(&checker->arena, left_base_t);
          CheckerError(checker, node->marker, "The left expression is not a struct or union type, it is a '%.*s'\n", str_expand(t));
        } else {
          accessed_type = left_base_t;
        }
      }
      
      if (!accessed_type) {
        node->expr_type = type_refs[Type_Index_None];
        return;
      }
      
      Token_node* curr_name = accessed_type->compound_t.member_names.first;
      u32 found = 0;
      b8 success = false;
      for (; found < accessed_type->compound_t.member_names.node_count; found++) {
        if (str_eq(curr_name->token.lexeme, node->access.right.lexeme)) {
          success = true;
          break;
        }
        curr_name = curr_name->next;
      }
      
      if (!success) {
        string t = Debug_GetTypeString(&checker->arena, accessed_type);
        CheckerError(checker, node->marker, "The type '%.*s' does not have the member '%.*s'\n", str_expand(t), str_expand(node->access.right.lexeme));
        return;
      }
      
      node->expr_type = accessed_type->compound_t.member_ts[found];
    } break;
    
    case NT_Type_Integer: {
      u32 index = Type_Index_I32;
      if (!node->int_type.is_signed)
        index = Type_Index_U32;
      if (node->int_type.size == 64) {
        if (index == Type_Index_I32)
          index = Type_Index_I64;
        else
          index = Type_Index_U64;
      }
      node->constant_val.type_lit = type_refs[index];
      node->expr_type = type_refs[Type_Index_Type];
    } break;
    
    case NT_Type_Float: {
      u32 index = node->float_type.size == 64 ? Type_Index_F64 : Type_Index_F32;
      node->constant_val.type_lit = type_refs[index];
      node->expr_type = type_refs[Type_Index_Type];
    } break;
    
    case NT_Type_Void: {
      node->constant_val.type_lit = type_refs[Type_Index_Void];
      node->expr_type = type_refs[Type_Index_Type];
    } break;
    
    case NT_Type_Pointer: {
      Checker_CheckOuter(checker, node->pointer_type.sub);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !node->pointer_type.sub->is_constant || node->pointer_type.sub->constant_val.type != CVT_Type) {
        string t = Debug_GetTypeString(&checker->arena, node->pointer_type.sub->expr_type);
        CheckerError(checker, node->marker, "The pointer type modifer only applies to a type not a '%.*s'\n", str_expand(t));
      }
      
      node->expr_type = type_refs[Type_Index_Type];
      node->constant_val.type_lit = push_pointer_type(checker, node->pointer_type.sub->constant_val.type_lit);
    } break;
    
    case NT_Type_Array: {
      Checker_CheckOuter(checker, node->array_type.sub);
      Checker_CheckOuter(checker, node->array_type.count);
      
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !node->array_type.sub->is_constant || node->array_type.sub->constant_val.type != CVT_Type) {
        string t = Debug_GetTypeString(&checker->arena, node->array_type.sub->expr_type);
        CheckerError(checker, node->marker, "The array type modifer only applies to a type not a '%.*s'\n", str_expand(t));
      }
      CheckerAssertion(checker, !node->array_type.count->is_constant || node->array_type.count->constant_val.type != CVT_Int) {
        CheckerError(checker, node->marker, "Size of an array type must be a compile time constant\n");
      }
      
      node->expr_type = type_refs[Type_Index_Type];
      node->constant_val.type_lit = push_array_type(checker, node->array_type.sub->constant_val.type_lit, node->array_type.count->constant_val.int_lit);
    } break;
    
    
    case NT_Type_Func: {
      Checker_CheckOuter(checker, node->func_type.return_type);
      
      ASTNode* curr = node->func_type.arg_types;
      while (curr) {
        Checker_CheckOuter(checker, curr);
        curr = curr->next;
      }
      
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = type_refs[Type_Index_Type];
      
      curr = node->func_type.arg_types;
      while (curr) {
        CheckerAssertion(checker, !curr->is_constant || curr->constant_val.type != CVT_Type) {
          string instead = Debug_GetTypeString(&checker->arena, curr->expr_type);
          CheckerError(checker, curr->marker, "Function Arguments should be constant types, instead we got a '%.*s'\n", str_expand(instead));
        }
        curr = curr->next;
      }
      
      ValueTypeBucket* ty = nullptr;
      if (stable_table_get(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache,
                           node, &ty))  {
        node->constant_val.type_lit = ty->type;
        return;
      }
      
      ValueTypeBucket bucket = {0};
      bucket.type = pool_alloc(&checker->allocator);
      bucket.type->type = TK_Func;
      bucket.type->func_t.ret_t = node->func_type.return_type->constant_val.type_lit;
      bucket.type->func_t.arg_ts =
        arena_alloc(&checker->arena, sizeof(ValueType*) * node->func_type.arity);
      bucket.type->func_t.arity = node->func_type.arity;
      
      curr = node->func_type.arg_types;
      for (int i = 0; i < node->func_type.arity; i++) {
        bucket.type->func_t.arg_ts[i] = curr->constant_val.type_lit;
        curr = curr->next;
      }
      
      stable_table_set(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache,
                       node, bucket);
      
      node->constant_val.type_lit = bucket.type;
    } break;
    
    case NT_Type_Struct:
    case NT_Type_Union: {
      ASTNode* curr = node->compound_type.member_types;
      while (curr) {
        Checker_CheckOuter(checker, curr);
        curr = curr->next;
      }
      
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = type_refs[Type_Index_Type];
      
      
      curr = node->compound_type.member_types;
      while (curr) {
        CheckerAssertion(checker, !curr->is_constant || curr->constant_val.type != CVT_Type) {
          string instead = Debug_GetTypeString(&checker->arena, curr->expr_type);
          CheckerError(checker, curr->marker, "Struct/Union members should be constant types, instead we got a '%.*s'\n", str_expand(instead));
        }
        curr = curr->next;
      }
      
      
      ValueTypeBucket* ty = nullptr;
      if (stable_table_get(ASTCompoundTypeRef, ValueTypeBucket,
                           &checker->compound_type_cache, node, &ty)) {
        node->constant_val.type_lit = ty->type;
        return;
      }
      
      ValueTypeBucket bucket = {0};
      bucket.type = pool_alloc(&checker->allocator);
      bucket.type->type = node->type == NT_Type_Struct ? TK_Struct : TK_Union;
      bucket.type->compound_t.member_ts = arena_alloc(&checker->arena, sizeof(ValueType*) *
                                                      node->compound_type.member_count);
      bucket.type->compound_t.member_names = node->compound_type.member_names;
      bucket.type->compound_t.count = node->compound_type.member_count;
      
      curr = node->compound_type.member_types;
      for (int i = 0; i < node->compound_type.member_count; i++) {
        bucket.type->compound_t.member_ts[i] = curr->constant_val.type_lit;
        curr = curr->next;
      }
      
      stable_table_set(ASTCompoundTypeRef, ValueTypeBucket,
                       &checker->compound_type_cache, node, bucket);
      
      node->constant_val.type_lit = bucket.type;
    } break;
    
    case NT_Stmt_Assign: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->binary_op.left);
      Checker_CheckOuter(checker, node->binary_op.right);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->binary_op.left->expr_type, node->binary_op.right->expr_type)) {
        string left  = Debug_GetTypeString(&checker->arena, node->binary_op.left->expr_type);
        string right = Debug_GetTypeString(&checker->arena, node->binary_op.right->expr_type);
        CheckerError(checker, node->marker, "The LHS and RHS for the binary operator should have the same types, but we got %.*s and %.*s instead\n",
                     str_expand(left), str_expand(right));
      }
      
      CheckerAssertion(checker, !is_lvalue(node->addr)) {
        CheckerError(checker, node->marker, "You can only assign to expressions that have an address, but the one being assigned to does not\n");
      }
      
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Stmt_Expr: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->expr_stmt);
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Stmt_Block: {
      CheckerSetCurrentStatement(checker, node);
      
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Stmt_While: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->while_loop.condition);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->while_loop.condition->expr_type, type_refs[Type_Index_Bool])) {
        string condition = Debug_GetTypeString(&checker->arena, node->while_loop.condition->expr_type);
        CheckerError(checker, node->marker, "Condition for the while loop should be a bool but we got a '%.*s' instead",
                     str_expand(condition));
      }
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Stmt_If: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->if_stmt.condition);
      CheckerReturnIfIdentDNF(checker);
      
      CheckerAssertion(checker, !CheckAbsolute(node->if_stmt.condition->expr_type, type_refs[Type_Index_Bool])) {
        string condition = Debug_GetTypeString(&checker->arena, node->if_stmt.condition->expr_type);
        CheckerError(checker, node->marker, "Condition for the if statement should be a bool but we got a '%.*s' instead",
                     str_expand(condition));
      }
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Stmt_Return: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->return_stmt);
      CheckerReturnIfIdentDNF(checker);
      
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    case NT_Decl: {
      CheckerSetCurrentStatement(checker, node);
      
      Checker_CheckOuter(checker, node->decl.type);
      Checker_CheckOuter(checker, node->decl.val);
      CheckerReturnIfIdentDNF(checker);
      
      ValueType* typ;
      if (node->decl.val)
        typ = node->decl.val->expr_type;
      
      if (node->decl.type) {
        CheckerAssertion(checker, !CheckAbsolute(node->decl.type->expr_type, type_refs[Type_Index_Type])) {
          string decltype = Debug_GetTypeString(&checker->arena, node->decl.type->expr_type);
          CheckerError(checker, node->decl.type->marker, "The type expression in this declaration does not resolve to a type, it resolves to a '%.*s'\n",
                       str_expand(decltype));
        }
        
        if (node->decl.val) {
          CheckerAssertion(checker, !CheckAbsolute(node->decl.type->constant_val.type_lit, node->decl.val->expr_type)) {
            string decltype = Debug_GetTypeString(&checker->arena, node->decl.type->constant_val.type_lit);
            string declval = Debug_GetTypeString(&checker->arena, node->decl.val->expr_type);
            CheckerError(checker, node->decl.type->marker, "The type expression in this declaration '%.*s', does not match the type of the value expression '%.*s'\n",
                         str_expand(decltype), str_expand(declval));
          }
        }
        
        typ = node->decl.type->constant_val.type_lit;
      }
      
      node->decl.resolved_type = typ;
      
      Symbol k = (Symbol) {
        .ident = node->decl.ident,
        .scope = checker->scope,
        .type = typ,
        .is_constant = node->decl.is_constant,
      };
      
      if (node->decl.val && k.is_constant)
        k.constant_val = node->decl.val->constant_val;
      
      i32 idx = -1;
      for (i32 i = checker->symbols.len-1; i >= 0; i--) {
        if (checker->symbols.elems[i].scope != checker->scope) break;
        if (str_eq(checker->symbols.elems[i].ident.lexeme, k.ident.lexeme)) {
          idx = i;
        }
      }
      if (idx != -1) {
        CheckerError(checker, node->marker, "Redeclaration of symbol '%.*s'\n", str_expand(k.ident.lexeme));
      }
      
#if defined(PRINT_ON_SYMBOL_REGISTER)
      string tn = Debug_GetTypeString(&checker->arena, k.type);
      printf("Registered Symbol %.*s: %.*s\n", str_expand(k.ident.lexeme),
             str_expand(tn));
#endif
      
      darray_add(Symbol, &checker->symbols, k);
      
      node->expr_type = type_refs[Type_Index_None];
    } break;
    
    default: {
      node->expr_type = type_refs[Type_Index_None];
    } break;
  }
  
}

static void Checker_CheckNode(Checker* checker, ASTNode* node) {
  Checker_CheckOuter(checker, node);
  Checker_CheckInner(checker, node);
}

//~ Checker

void Checker_Init(Checker* checker) {
  pool_init(&checker->allocator, sizeof(ValueType));
  arena_init(&checker->arena);
  stable_table_init(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache, 32);
  stable_table_init(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache,
                    32);
  stable_table_init(ASTCompoundTypeRef, ValueTypeBucket,
                    &checker->compound_type_cache, 32);
  stable_table_init(ASTNodeRef, StringArrayBucket, &checker->pending_nodes, 32);
  
  type_refs[Type_Index_I32] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_I32]->type = TK_Int;
  type_refs[Type_Index_I32]->int_t.size = 32;
  type_refs[Type_Index_I32]->int_t.is_signed = true;
  
  type_refs[Type_Index_I64] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_I64]->type = TK_Int;
  type_refs[Type_Index_I64]->int_t.size = 64;
  type_refs[Type_Index_I64]->int_t.is_signed = true;
  
  type_refs[Type_Index_U32] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_U32]->type = TK_Int;
  type_refs[Type_Index_U32]->int_t.size = 32;
  type_refs[Type_Index_U32]->int_t.is_signed = false;
  
  type_refs[Type_Index_U64] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_U64]->type = TK_Int;
  type_refs[Type_Index_U64]->int_t.size = 64;
  type_refs[Type_Index_U64]->int_t.is_signed = false;
  
  type_refs[Type_Index_F32] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_F32]->type = TK_Float;
  type_refs[Type_Index_F32]->float_t.size = 32;
  
  type_refs[Type_Index_F64] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_F64]->type = TK_Float;
  type_refs[Type_Index_F64]->float_t.size = 32;
  
  type_refs[Type_Index_Type] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_Type]->type = TK_Type;
  
  type_refs[Type_Index_Void] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_Void]->type = TK_Void;
  
  type_refs[Type_Index_Bool] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_Bool]->type = TK_Bool;
  
  type_refs[Type_Index_None] = pool_alloc(&checker->allocator);
  type_refs[Type_Index_None]->type = TK_None;
}

void Checker_Check(Checker* checker, ASTNode* tree) {
  checker->tree = tree;
  checker->ident_guarantee = false;
  
  ASTNode* curr = tree;
  while (curr) {
    Checker_CheckOuter(checker, curr);
    curr = curr->next;
  }
  
  checker->ident_guarantee = true;
  b8 changed = true;
  while (changed && checker->pending_nodes.count) {
    changed = false;
    
    // Iterate through pending identifiers and possibly resolve them all
    Iterate (checker->pending_nodes, i) {
      StringArrayBucket* bucket = &checker->pending_nodes.elems[i];
      if (ast_node_is_null(bucket->key)) continue;
      
      while (bucket) {
        u32 idx;
        b8 available = true;
        Iterate(bucket->strings, k) {
          if (!IdentifierLookup(checker, bucket->strings.elems[k], &idx))
            available = false;
        }
        if (available) {
          if (bucket->key->type == NT_Decl) changed = true;
          Checker_CheckOuter(checker, bucket->key);
          stable_table_del(ASTNodeRef, StringArrayBucket, &checker->pending_nodes, bucket->key);
        }
        
        bucket = bucket->hash_next;
      }
    }
  }
  checker->ident_guarantee = false;
  
  if (checker->pending_nodes.count) {
    CheckerError(checker, tree->marker, "Put a better error message here.. There was at least one unidentified identifier");
    return;
  }
  
  curr = tree;
  while (curr) {
    Checker_CheckInner(checker, curr);
    curr = curr->next;
  }
}

void Checker_Free(Checker* checker) {
  pool_free(&checker->allocator);
  arena_init(&checker->arena);
  stable_table_free(ASTFuncRef, ValueTypeBucket, &checker->func_type_cache);
  stable_table_free(ModdedTypeKey, ModdedValueTypeBucket, &checker->modded_type_cache);
  stable_table_free(ASTCompoundTypeRef, ValueTypeBucket, &checker->compound_type_cache);
  stable_table_free(ASTNodeRef, StringArrayBucket, &checker->pending_nodes);
  darray_free(Symbol, &checker->symbols);
}

//~ Debug

string Debug_GetTypeString(M_Arena* arena, ValueType* type) {
  if (!type) {
    return str_lit("void");
  }
  
  switch (type->type) {
    case TK_None: return str_lit("none");
    case TK_Void: return str_lit("void");
    case TK_Bool: return str_lit("bool");
    case TK_Int:  return str_from_format(arena,
                                         "%s%d", type->int_t.is_signed ? "i" : "u",
                                         type->int_t.size);
    case TK_Float: return str_from_format(arena, "f%d", type->float_t.size);
    case TK_Type: return str_lit("type"); break;
    
    case TK_Pointer: return str_cat(arena, str_lit("^"), Debug_GetTypeString(arena, type->ptr_t.sub_t));
    case TK_Array: {
      string subtype = Debug_GetTypeString(arena, type->ptr_t.sub_t);
      return str_from_format(arena, "[%llu]%.*s", type->array_t.count, str_expand(subtype));
    } break;
    
    case TK_Struct:
    case TK_Union: {
      string_list sl = {0};
      string_list_push(arena, &sl, type->type == TK_Struct
                       ? str_lit("struct { ")
                       : str_lit("union { "));
      for (u64 i = 0; i < type->compound_t.count; i++) {
        string_list_push(arena, &sl, Debug_GetTypeString(arena, type->compound_t.member_ts[i]));
        string_list_push(arena, &sl, str_lit("; "));
      }
      string_list_push(arena, &sl, str_lit("}"));
      
      return string_list_flatten(arena, &sl);
    } break;
    
    case TK_Func: {
      string_list sl = {0};
      string_list_push(arena, &sl, str_lit("func ("));
      for (u32 i = 0; i < type->func_t.arity; i++) {
        string_list_push(arena, &sl, Debug_GetTypeString(arena, type->func_t.arg_ts[i]));
        if (i != type->func_t.arity-1) string_list_push(arena, &sl, str_lit(","));
      }
      string_list_push(arena, &sl, str_lit(") -> "));
      string_list_push(arena, &sl, Debug_GetTypeString(arena, type->func_t.ret_t));
      return string_list_flatten(arena, &sl);
    } break;
    
    default: {
      return str_from_format(arena, "Got something weird: %u\n", type->type);
    } break;
  }
}
