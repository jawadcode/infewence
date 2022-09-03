use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
};

use crate::expr::{Expr, Ident, Lit};

trait Types {
    /// Returns the set of *f*ree *t*ype *v*ariables in `self`
    fn ftv(&self) -> HashSet<Ident>;

    /// Apply the substitution `subst` to `self`
    fn apply(&self, subst: &Subst) -> Self;
}

impl Lit {
    fn infer(&self) -> (Subst, Type) {
        (
            Subst::default(),
            match self {
                Lit::Int(_) => Type::Int,
                Lit::Bool(_) => Type::Bool,
            },
        )
    }
}

/// A type expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    /// The type of a variable
    Var(Ident),
    /// An integer
    Int,
    /// A boolean
    Bool,
    /// The type of a function, usually represented in the form: `in → out`
    Fun { in_: Box<Self>, out: Box<Self> },
}

impl Types for Type {
    fn ftv(&self) -> HashSet<Ident> {
        match self {
            // `FV(x) = {x}`
            Type::Var(var) => HashSet::from([var.clone()]),
            // `FV(T → T') = FV(T) ∪ FV(T')`
            Type::Fun { in_, out } => in_.ftv().union(&out.ftv()).cloned().collect(),
            // Primitive types have no free type variables
            _ => HashSet::new(),
        }
    }

    fn apply(&self, subst: &Subst) -> Type {
        match self {
            // Return either the result of the substitution or just itself
            Type::Var(var) => subst.lookup(var).unwrap_or(Type::Var(var.clone())),
            // Return a new function where both type arguments have had the substitution applied
            Type::Fun { in_, out } => Type::Fun {
                in_: Box::new(in_.apply(subst)),
                out: Box::new(out.apply(subst)),
            },
            // Primitive types don't need to be substituted
            t => t.clone(),
        }
    }
}

fn var_bind(ident: &Ident, ty: &Type) -> Subst {
    if ty == &Type::Var(ident.clone()) {
        Subst::default()
    } else if ty.ftv().contains(ident) {
        panic!("Occurs check fails: {ident} vs. {:?}", ty)
    } else {
        Subst(HashMap::from([(ident.clone(), ty.clone())]))
    }
}

impl Type {
    /// Returns the Most General Unifier of `self` and `other`, a unifier is a substitution S where
    /// `S(t1) == S(t2)`
    fn mgu(&self, other: &Type) -> Subst {
        use Type::*;
        match (self, other) {
            (Fun { in_: i0, out: o0 }, Fun { in_: i1, out: o1 }) => {
                let s1 = i0.mgu(&i1);
                let s2 = o0.apply(&s1).mgu(&o1.apply(&s1));
                s2.compose(&s1)
            }
            (Var(u), t) => var_bind(u, t),
            (t, Var(u)) => var_bind(u, t),
            (Int, Int) | (Bool, Bool) => Subst::default(),
            (t1, t2) => panic!("Types do not unify: {:?} vs. {:?}", t1, t2),
        }
    }
}

/// A type scheme, aka a Polytype
#[derive(Clone)]
struct Scheme {
    names: HashSet<Ident>,
    ty: Type,
}

impl Scheme {
    fn instantiate(&self, gen: &mut TypeVarGen) -> Type {
        let new_vars = self.names.iter().map(|_| gen.new_var());
        self.ty
            .apply(&Subst(self.names.iter().cloned().zip(new_vars).collect()))
    }
}

#[derive(Clone)]
struct Subst(HashMap<Ident, Type>);

impl Default for Subst {
    fn default() -> Self {
        Self(HashMap::new())
    }
}

impl Subst {
    /// Compose `self` with `s2` by unioning `self` with the substitution created by the application of `self` to every type in `other`
    fn compose(&self, s2: &Self) -> Self {
        let (Self(s1), Self(s2)) = (self, s2);
        let s2: HashMap<Ident, Type> = s2.iter().map(|(k, v)| (k.clone(), v.apply(self))).collect();
        let s3 = s1.union(&s2);
        Subst(s3)
    }

    /// Lookup `ident` in `self`
    fn lookup(&self, ident: &Ident) -> Option<Type> {
        let Self(s) = self;
        s.get(ident).map(Clone::clone)
    }

    // Return a clone of `self` with `idents` removed
    fn remove(&self, idents: &HashSet<Ident>) -> Self {
        let mut sub = self.clone();
        for ident in idents {
            sub.0.remove(ident);
        }
        sub
    }
}

impl Types for Scheme {
    fn ftv(&self) -> HashSet<Ident> {
        self.ty.ftv().difference(&self.names).cloned().collect()
    }

    fn apply(&self, subst: &Subst) -> Self {
        Self {
            names: self.names.clone(),
            ty: {
                let sub = subst.remove(&self.names);
                self.ty.apply(&sub)
            },
        }
    }
}

impl<T: Types> Types for Vec<T> {
    fn ftv(&self) -> HashSet<Ident> {
        self.iter()
            .map(Types::ftv)
            .fold(HashSet::new(), |acc, hs| acc.union(&hs).cloned().collect())
    }

    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }
}

// The type environment, usually denoted by `Γ` in type theory notation
#[derive(Clone, Default)]
pub struct TypeEnv(HashMap<Ident, Scheme>);

impl TypeEnv {
    fn insert(&self, ident: &Ident, scheme: &Scheme) -> Self {
        let Self(mut env) = self.clone();
        env.insert(ident.clone(), scheme.clone());
        Self(env)
    }

    fn remove(&self, ident: &Ident) -> Self {
        let Self(mut env) = self.clone();
        env.remove(ident);
        Self(env)
    }

    fn generalize(&self, ty: &Type) -> Scheme {
        let names: HashSet<Ident> = ty.ftv().difference(&self.ftv()).cloned().collect();
        Scheme {
            names,
            ty: ty.clone(),
        }
    }

    pub fn infer_type(&self, expr: &Expr) -> Type {
        let mut gen = TypeVarGen::default();
        let (subst, ty) = self.infer(&mut gen, expr);
        ty.apply(&subst)
    }

    fn infer(&self, gen: &mut TypeVarGen, expr: &Expr) -> (Subst, Type) {
        match (self, expr) {
            (TypeEnv(env), Expr::Var(var)) => match env.get(var) {
                Some(sigma) => (Subst::default(), sigma.instantiate(gen)),
                None => panic!("Unbounsubstitutiond variable: {var}"),
            },
            (_, Expr::Lit(lit)) => lit.infer(),
            (env, Expr::Abs { arg, body }) => {
                let typevar = gen.new_var();
                let env1 = env.remove(&arg);
                let env2 = Self(env1.0.union(&HashMap::from([(
                    arg.clone(),
                    Scheme {
                        names: HashSet::new(),
                        ty: typevar.clone(),
                    },
                )])));
                let (s1, t1) = env2.infer(gen, body);
                (
                    s1.clone(),
                    Type::Fun {
                        in_: Box::new(typevar.apply(&s1)),
                        out: Box::new(t1),
                    },
                )
            }
            (env, Expr::App { fun, arg }) => {
                let typevar = gen.new_var();
                let (s1, t1) = env.infer(gen, fun);
                let (s2, t2) = env.apply(&s1).infer(gen, arg);
                let s3 = t1.apply(&s2).mgu(&Type::Fun {
                    in_: Box::new(t2),
                    out: Box::new(typevar.clone()),
                });
                (s3.compose(&s2).compose(&s1), typevar.apply(&s3))
            }
            (env, Expr::Let { name, value, body }) => {
                let (s1, t1) = env.infer(gen, &value);
                let env1 = env.remove(name);
                let ta = env.apply(&s1).generalize(&t1);
                let env2 = env1.insert(name, &ta);
                let (s2, t2) = env2.apply(&s1).infer(gen, body);
                (s2.compose(&s1), t2)
            }
        }
    }
}

impl Types for TypeEnv {
    fn ftv(&self) -> HashSet<Ident> {
        let Self(env) = self;
        env.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    fn apply(&self, subst: &Subst) -> Self {
        let Self(mut env) = self.clone();
        for ty in env.values_mut() {
            *ty = ty.apply(subst);
        }
        Self(env)
    }
}

/// An unbound type
pub struct TypeVar(usize);

impl Display for TypeVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'t{}", self.0)
    }
}

pub struct TypeVarGen {
    supply: usize,
}

impl Default for TypeVarGen {
    fn default() -> Self {
        Self { supply: 0 }
    }
}

impl TypeVarGen {
    pub fn new_var(&mut self) -> Type {
        let var = TypeVar(self.supply);
        self.supply += 1;
        Type::Var(var.to_string())
    }
}

trait Union {
    fn union(&self, other: &Self) -> Self;
}

/// Implement union for HashMap such that the value in `self` is used over the value in `other` in
/// the event of a collision.
impl<K, V> Union for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn union(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (key, value) in other {
            res.entry(key.clone()).or_insert(value.clone());
        }
        res
    }
}
