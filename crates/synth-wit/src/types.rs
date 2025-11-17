//! Type system utilities for WIT

use crate::ast::Type;

/// Type context for type checking
#[derive(Debug, Clone)]
pub struct TypeContext {
    types: std::collections::HashMap<String, Type>,
}

impl TypeContext {
    pub fn new() -> Self {
        Self {
            types: std::collections::HashMap::new(),
        }
    }

    pub fn insert(&mut self, name: String, ty: Type) {
        self.types.insert(name, ty);
    }

    pub fn get(&self, name: &str) -> Option<&Type> {
        self.types.get(name)
    }

    pub fn resolve(&self, ty: &Type) -> Type {
        match ty {
            Type::Named(name) => {
                if let Some(resolved) = self.get(name) {
                    self.resolve(resolved)
                } else {
                    ty.clone()
                }
            }
            Type::List(inner) => Type::List(Box::new(self.resolve(inner))),
            Type::Option(inner) => Type::Option(Box::new(self.resolve(inner))),
            Type::Result { ok, err } => Type::Result {
                ok: ok.as_ref().map(|t| Box::new(self.resolve(t))),
                err: err.as_ref().map(|t| Box::new(self.resolve(t))),
            },
            Type::Tuple(types) => {
                Type::Tuple(types.iter().map(|t| self.resolve(t)).collect())
            }
            _ => ty.clone(),
        }
    }
}

impl Default for TypeContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Calculate the flattened size of a type for ABI purposes
pub fn flattened_size(ty: &Type, ctx: &TypeContext) -> usize {
    let resolved = ctx.resolve(ty);

    match resolved {
        // Primitives are 1 value
        ty if ty.is_primitive() => 1,

        // Strings are (ptr, len) = 2 values
        Type::String => 2,

        // Lists are (ptr, len) = 2 values
        Type::List(_) => 2,

        // Options are (discriminant, value) = 1 + value_size
        Type::Option(inner) => 1 + flattened_size(&inner, ctx),

        // Results are (discriminant, max(ok, err))
        Type::Result { ok, err } => {
            let ok_size = ok.as_ref().map(|t| flattened_size(t, ctx)).unwrap_or(0);
            let err_size = err.as_ref().map(|t| flattened_size(t, ctx)).unwrap_or(0);
            1 + ok_size.max(err_size)
        }

        // Tuples are sum of all elements
        Type::Tuple(types) => types.iter().map(|t| flattened_size(t, ctx)).sum(),

        // Named types - should be resolved already
        Type::Named(_) => 1, // Fallback

        // Generics - size unknown
        Type::Generic(_) => 1,

        _ => 1,
    }
}

/// Check if type can be flattened (passed in registers)
pub fn can_flatten(ty: &Type, ctx: &TypeContext) -> bool {
    const MAX_FLAT_PARAMS: usize = 16;
    flattened_size(ty, ctx) <= MAX_FLAT_PARAMS
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_flattened_size_primitives() {
        let ctx = TypeContext::new();

        assert_eq!(flattened_size(&Type::U32, &ctx), 1);
        assert_eq!(flattened_size(&Type::S32, &ctx), 1);
        assert_eq!(flattened_size(&Type::F32, &ctx), 1);
        assert_eq!(flattened_size(&Type::Bool, &ctx), 1);
    }

    #[test]
    fn test_flattened_size_string() {
        let ctx = TypeContext::new();
        assert_eq!(flattened_size(&Type::String, &ctx), 2); // ptr + len
    }

    #[test]
    fn test_flattened_size_list() {
        let ctx = TypeContext::new();
        let list_type = Type::List(Box::new(Type::U8));
        assert_eq!(flattened_size(&list_type, &ctx), 2); // ptr + len
    }

    #[test]
    fn test_flattened_size_option() {
        let ctx = TypeContext::new();
        let opt_type = Type::Option(Box::new(Type::U32));
        assert_eq!(flattened_size(&opt_type, &ctx), 2); // discriminant + value
    }

    #[test]
    fn test_flattened_size_result() {
        let ctx = TypeContext::new();
        let result_type = Type::Result {
            ok: Some(Box::new(Type::U32)),
            err: Some(Box::new(Type::String)),
        };
        // discriminant + max(1, 2) = 1 + 2 = 3
        assert_eq!(flattened_size(&result_type, &ctx), 3);
    }

    #[test]
    fn test_flattened_size_tuple() {
        let ctx = TypeContext::new();
        let tuple_type = Type::Tuple(vec![Type::U32, Type::U32, Type::F32]);
        assert_eq!(flattened_size(&tuple_type, &ctx), 3);
    }

    #[test]
    fn test_can_flatten() {
        let ctx = TypeContext::new();

        // Small types can be flattened
        assert!(can_flatten(&Type::U32, &ctx));
        assert!(can_flatten(&Type::String, &ctx));

        // Large tuples cannot
        let big_tuple = Type::Tuple(vec![Type::U32; 20]);
        assert!(!can_flatten(&big_tuple, &ctx));
    }

    #[test]
    fn test_type_resolution() {
        let mut ctx = TypeContext::new();

        // Define a type alias
        ctx.insert("my-int".to_string(), Type::S32);

        let named = Type::Named("my-int".to_string());
        let resolved = ctx.resolve(&named);

        assert_eq!(resolved, Type::S32);
    }
}
