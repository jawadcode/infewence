use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    ops::Sub,
};

type Ident = String;

/// A lambda calculus expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Expr {
    /// References a variable which is in scope
    Var(Ident),
    /// A literal expression, e.g. `123` or `false`
    Lit(Lit),
    /// A function application, usually represented in the form: `fun arg` where `fun` is called
    /// with `arg`
    App { fun: Box<Self>, arg: Box<Self> },
    /// A function abstraction, usually represented in the form: `λarg. body`, i.e. an anonymous
    /// function which takes in `arg` and returns `body`
    Abs { arg: Ident, body: Box<Self> },
    /// A let-binding, usually represented in the form: `let name = value in body`, where a new
    /// scope is introduced which contains a variable `name` with the value `body` for the
    /// expression `body`
    Let {
        name: Ident,
        value: Box<Self>,
        body: Box<Self>,
    },
}

/// A literal expression
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Lit {
    /// An integer literal, e.g. `123`
    Int(i64),
    /// A boolean literal: `true` or `false`
    Bool(bool),
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
enum Type {
    /// The type of a variable
    Var(Ident),
    /// An integer
    Int,
    /// A boolean
    Bool,
    /// The type of a function, usually represented in the form: `in → out`
    Fun { in_: Box<Self>, out: Box<Self> },
}

fn var_bind(ident: &Ident, ty: &Type) -> Subst {
    if ty == &Type::Var(ident.clone()) {
        Subst::default()
    } else if ty.free_type_vars().contains(ident) {
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

trait Types {
    /// Returns the set of free variables in `self`
    fn free_type_vars(&self) -> HashSet<Ident>;

    /// Apply the substitution `subst` to `self`
    fn apply(&self, subst: &Subst) -> Self;
}

#[derive(Clone)]
struct Subst(HashMap<Ident, Type>);

impl Default for Subst {
    fn default() -> Self {
        Self(HashMap::new())
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

impl Types for Type {
    fn free_type_vars(&self) -> HashSet<Ident> {
        match self {
            // `FV(x) = {x}`
            Type::Var(var) => HashSet::from([var.clone()]),
            // `FV(T → T') = FV(T) ∪ FV(T')`
            Type::Fun { in_, out } => in_
                .free_type_vars()
                .union(&out.free_type_vars())
                .cloned()
                .collect(),
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

impl Types for Scheme {
    fn free_type_vars(&self) -> HashSet<Ident> {
        self.ty
            .free_type_vars()
            .difference(&self.names)
            .cloned()
            .collect()
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
    fn free_type_vars(&self) -> HashSet<Ident> {
        self.iter()
            .map(Types::free_type_vars)
            .fold(HashSet::new(), |acc, hs| acc.union(&hs).cloned().collect())
    }

    fn apply(&self, subst: &Subst) -> Self {
        self.iter().map(|t| t.apply(subst)).collect()
    }
}

// The type environment, usually denoted by `Γ` in type theory notation
#[derive(Clone)]
struct TypeEnv(HashMap<Ident, Scheme>);

impl TypeEnv {
    fn remove(&self, ident: &Ident) -> Self {
        let Self(mut env) = self.clone();
        env.remove(ident);
        Self(env)
    }

    fn generalize(&self, ty: &Type) -> Scheme {
        let names: HashSet<Ident> = ty
            .free_type_vars()
            .difference(&self.free_type_vars())
            .cloned()
            .collect();
        Scheme {
            names,
            ty: ty.clone(),
        }
    }

    fn infer(&self, gen: &mut TypeVarGen, expr: &Expr) -> (Subst, Type) {
        match (self, expr) {
            (TypeEnv(env), Expr::Var(var)) => match env.get(var) {
                Some(sigma) => (Subst::default(), sigma.instantiate(gen)),
                None => panic!("Unbound variable: {var}"),
            },
            (_, Expr::Lit(lit)) => lit.infer(),
            (env, Expr::Abs { arg, body }) => {
                let typevar = gen.new_var();
                let env1 = self.remove(&arg);
                let env2 = Self(env1.0.union(&HashMap::from([(
                    arg.clone(),
                    Scheme {
                        names: HashSet::new(),
                        ty: typevar,
                    },
                )])));
                let (s1, t1) = env2.infer(gen, body);
                (
                    s1,
                    Type::Fun {
                        in_: todo!(),
                        out: todo!(),
                    },
                )
            }
            _ => unimplemented!(),
        }
    }
}

impl Types for TypeEnv {
    fn free_type_vars(&self) -> HashSet<Ident> {
        let Self(env) = self;
        env.values()
            .cloned()
            .collect::<Vec<Scheme>>()
            .free_type_vars()
    }

    fn apply(&self, subst: &Subst) -> Self {
        let Self(mut env) = self.clone();
        for ty in env.values_mut() {
            *ty = ty.apply(subst);
        }
        Self(env)
    }
}

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
