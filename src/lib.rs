//! Model for (a subset of) LLVM 19.0.0.
//! see [https://llvm.org/docs/LangRef.html]

#![warn(missing_debug_implementations)]

use itertools::Itertools;
use std::fmt::Display;

/// A LLVM local identifier
///
/// ```
/// # use llvm::*;
/// let local = Uid::new("x");
/// assert_eq!(local.to_string(), "%x");
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Uid(String);

/// A LLVM global identifier
///
/// ```
/// # use llvm::*;
/// let global = Gid::new("main");
/// assert_eq!(global.to_string(), "@main");
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Gid(String);

/// A named type
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Tid(String);

/// A Label
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Label(String);

impl Uid {
    /// Constructs a new `Uid`
    pub fn new<S>(s: S) -> Self
    where
        S: ToString,
    {
        // TODO print escaped with quotes
        Self(s.to_string())
    }
}

impl Gid {
    /// Constructs a new `Gid`
    pub fn new<S>(s: S) -> Self
    where
        S: ToString,
    {
        // TODO print escaped with quotes
        Self(s.to_string())
    }
}

impl Tid {
    /// Constructs a new `Tid`
    pub fn new<S>(s: S) -> Self
    where
        S: ToString,
    {
        Self(s.to_string())
    }
}

impl Label {
    /// Constructs a new `Label`
    pub fn new<S>(s: S) -> Self
    where
        S: ToString,
    {
        Self(s.to_string())
    }
}

impl Display for Uid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for Gid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "@{}", self.0)
    }
}

impl Display for Tid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.0)
    }
}

impl Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[non_exhaustive]
/// A LLVM type (LLVM type system)[https://llvm.org/docs/LangRef.html#type-system]
pub enum Type {
    /// The void type. does not represent any value and has no size
    Void,
    /// The int type. does not represent any value and has no size
    Int(usize),
    /// Function signature type
    Fun(Vec<Type>, Box<Type>),
    /// The pointer type `ptr` is used to specify memory locations
    Ptr,
    /// The structure type is used to represent a collection of data members together in memory. The elements of a structure may be any type that has a size.
    Struct(Vec<Type>),
    /// Opaque structure types are used to represent structure types that do not have a body specified
    Opaque,
    /// The array type is a very simple derived type that arranges elements sequentially in memory
    Array(usize, Box<Type>),
    /// A reference to a named type, that has been defined before
    Named(Tid),
    // TODO: floating point
}

impl Type {
    /// constructs a new 64 bit integer
    pub fn i64() -> Self {
        Self::Int(64)
    }

    /// constructs a new 32 bit integer
    pub fn i32() -> Self {
        Self::Int(32)
    }

    /// constructs a new 16 bit integer
    pub fn i16() -> Self {
        Self::Int(16)
    }

    /// constructs a new 8 bit integer
    pub fn i8() -> Self {
        Self::Int(8)
    }

    /// constructs a new boolean. This is represented as a 1 bit integer.
    pub fn bool() -> Self {
        Self::Int(1)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Int(size) => write!(f, "i{size}"),
            Type::Fun(args, ret) => write!(f, "{} ({})", ret, args.iter().format(", ")),
            Type::Ptr => write!(f, "ptr"),
            Type::Opaque => write!(f, "opaque"),
            Type::Struct(ts) => write!(f, "{}", ts.iter().format(", ")),
            Type::Array(n, t) => write!(f, "[{n} x {t}]"),
            Type::Named(t) => write!(f, "{t}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Operand {
    Null,
    Id(Uid),
    Gid(Gid),
    ConstInt(i64),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Null => write!(f, "null"),
            Operand::Id(i) => write!(f, "{i}"),
            Operand::Gid(g) => write!(f, "{g}"),
            Operand::ConstInt(i) => write!(f, "{i}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Bop {
    Add,
    Sub,
    Mul,
    UDiv,
    SDiv,
    URem,
    SRem,
    Shl,
    LShr,
    AShr,
    And,
    Or,
    Xor,
}

impl Display for Bop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bop::Add => write!(f, "add"),
            Bop::Sub => write!(f, "sub"),
            Bop::Mul => write!(f, "mul"),
            Bop::UDiv => write!(f, "udiv"),
            Bop::SDiv => write!(f, "sdiv"),
            Bop::URem => write!(f, "urem"),
            Bop::SRem => write!(f, "srem"),
            Bop::Shl => write!(f, "shl"),
            Bop::LShr => write!(f, "lshr"),
            Bop::AShr => write!(f, "ashr"),
            Bop::And => write!(f, "and"),
            Bop::Or => write!(f, "or"),
            Bop::Xor => write!(f, "xor"),
        }
    }
}

/// type of comparison operator
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Cnd {
    Eq,
    Ne,
    UGt,
    UGe,
    ULt,
    Ule,
    SGt,
    SGe,
    SLt,
    SLe,
}

impl Display for Cnd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Cnd::Eq => write!(f, "eq"),
            Cnd::Ne => write!(f, "ne"),
            Cnd::UGt => write!(f, "ugt"),
            Cnd::UGe => write!(f, "uge"),
            Cnd::ULt => write!(f, "ult"),
            Cnd::Ule => write!(f, "ule"),
            Cnd::SGt => write!(f, "sgt"),
            Cnd::SGe => write!(f, "sge"),
            Cnd::SLt => write!(f, "slt"),
            Cnd::SLe => write!(f, "sle"),
        }
    }
}

/// instruction
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Insn {
    Binop(Bop, Type, Operand, Operand),
    ICmp(Cnd, Type, Operand, Operand),
    Alloca(Type),
    Load(Type, Operand),
    /// type src dest
    Store(Type, Operand, Operand),
    Call(Type, Operand, Vec<(Type, Operand)>),
    Gep(Type, Operand, Vec<Operand>),
    Bitcast(Type, Operand, Type),
    Comment(String),
}

impl Display for Insn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Insn::Binop(which, ty, op1, op2) => write!(f, "{which} {ty} {op1}, {op2}"),
            Insn::ICmp(cnd, ty, op1, op2) => write!(f, "icmp {cnd} {ty} {op1}, {op2}"),
            Insn::Alloca(ty) => write!(f, "alloca {ty}"),
            Insn::Load(ty, ptr) => write!(f, "load {ty}, ptr {ptr}"),
            Insn::Store(ty, src, dest) => write!(f, "store {ty} {src}, ptr {dest}"),
            Insn::Call(ty, fun, args) => {
                let args = args
                    .iter()
                    .format_with(", ", |(ty, op), f| f(&format_args!("{ty} {op}")));
                write!(f, "call {ty} {fun}({})", args)
            }
            Insn::Gep(ty, a, idx) if idx.is_empty() => {
                write!(f, "getelementptr {ty}, ptr {a}")
            }
            Insn::Gep(ty, a, indices) => {
                write!(
                    f,
                    "getelementptr {ty}, ptr {a}, {}",
                    indices
                        .iter()
                        .format_with(", ", |elt, f| f(&format_args!("i64 {elt}")))
                )
            }
            Insn::Bitcast(t1, op, t2) => write!(f, "bitcast {t1} {op} to {t2}"),
            Insn::Comment(s) => write!(f, "; {s}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Instruction(pub Uid, pub Insn);

impl Instruction {
    pub fn unnamed(insn: Insn) -> Self {
        Instruction(Uid::new("<unnamed>"), insn)
    }
}

impl Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1 {
            Insn::Store(_, _, _) | Insn::Comment(_) | Insn::Call(Type::Void, _, _) => {
                write!(f, "{}", self.1)
            }
            _ => write!(f, "{} = {}", self.0, self.1),
        }
    }
}

/// terminator instruction
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    RetVoid,
    Ret(Type, Operand),
    Br(Operand, Label, Label),
    BrUncond(Label),
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::RetVoid => write!(f, "ret void"),
            Term::Ret(ty, op) => write!(f, "ret {ty} {op}"),
            Term::Br(cnd, yes, no) => write!(f, "br i1 {cnd}, label %{yes}, label %{no}"),
            Term::BrUncond(to) => write!(f, "br label %{to}"),
        }
    }
}

/// block as defined by llvm
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Block {
    insns: Vec<Instruction>,
    term: Term,
}

impl Block {
    pub fn new(insns: Vec<Instruction>, term: Term) -> Self {
        Self { insns, term }
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for ins in &self.insns {
            writeln!(f, "    {ins}")?;
        }

        writeln!(f, "    {}", self.term)?;

        Ok(())
    }
}

/// control flow graph
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Cfg {
    entry: Block,
    labeled: Vec<(Label, Block)>,
}

impl Cfg {
    pub fn new(entry: Block, labeled: Vec<(Label, Block)>) -> Self {
        Self { entry, labeled }
    }
}

impl Display for Cfg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.entry)?;

        for (lbl, block) in &self.labeled {
            writeln!(f, "  {lbl}:")?;
            write!(f, "{block}")?;
        }

        Ok(())
    }
}

/// function declaration
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Fdecl {
    name: Gid,
    args: Vec<(Type, Uid)>,
    return_type: Type,
    body: Cfg,
}

impl Fdecl {
    pub fn new(name: Gid, args: Vec<(Type, Uid)>, return_type: Type, body: Cfg) -> Self {
        Self {
            name,
            args,
            return_type,
            body,
        }
    }
}

impl Display for Fdecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "define {} {}({}) {{",
            self.return_type,
            self.name,
            self.args
                .iter()
                .format_with(", ", |(ty, uid), f| f(&format_args!("{ty} {uid}")))
        )?;

        write!(f, "{}", self.body)?;

        write!(f, "}}")
    }
}

/// global initializer
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ginit {
    Null,
    Gid(Gid),
    ConstInt(i64),
    String(String),
    Array(Vec<Gdecl>),
    Struct(Vec<Gdecl>),
    Bitcast(Type, Box<Ginit>, Type),
    Zeroinit,
}

/// global declaration
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Gdecl {
    typ: Type,
    init: Ginit,
}

impl Gdecl {
    pub fn new(typ: Type, init: Ginit) -> Self {
        Self { typ, init }
    }
}
impl Display for Ginit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ginit::Null => write!(f, "null"),
            Ginit::Gid(g) => write!(f, "{g}"),
            Ginit::ConstInt(i) => write!(f, "{i}"),
            Ginit::String(s) => write!(f, r#"c"{}\00""#, s.escape_debug()),
            Ginit::Array(ts) => write!(f, "[ {} ]", ts.iter().format(", ")),
            Ginit::Struct(ts) => write!(f, "{{ {} }}", ts.iter().format(", ")),
            Ginit::Bitcast(t1, op, t2) => write!(f, "bitcast ({t1} {op} to {t2})"),
            Ginit::Zeroinit => write!(f, "zeroinitializer"),
        }
    }
}

impl Display for Gdecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.typ, self.init)
    }
}

/// program
#[derive(Default, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Program {
    type_decls: Vec<(Tid, Type)>,
    func_decls: Vec<Fdecl>,
    global_decls: Vec<(Gid, Gdecl)>,
    extern_decls: Vec<(Gid, Type)>,
}

impl Program {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_extern_decls(mut self, extern_decls: Vec<(Gid, Type)>) -> Self {
        self.extern_decls = extern_decls;
        self
    }

    pub fn with_global_decls(mut self, global_decls: Vec<(Gid, Gdecl)>) -> Self {
        self.global_decls = global_decls;
        self
    }

    pub fn with_type_decls(mut self, type_decls: Vec<(Tid, Type)>) -> Self {
        self.type_decls = type_decls;
        self
    }

    pub fn with_func_decls(mut self, func_decls: Vec<Fdecl>) -> Self {
        self.func_decls = func_decls;
        self
    }

    pub fn add_global_decl(&mut self, name: Gid, decl: Gdecl) -> &mut Self {
        self.global_decls.push((name, decl));
        self
    }

    pub fn add_func_decl(&mut self, fdecl: Fdecl) -> &mut Self {
        self.func_decls.push(fdecl);
        self
    }

    pub fn add_type_decl(mut self, name: Tid, typ: Type) -> Self {
        self.type_decls.push((name, typ));
        self
    }

    pub fn add_extern_decl(&mut self, name: Gid, typ: Type) -> &mut Self {
        self.extern_decls.push((name, typ));
        self
    }
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (tid, tdecl) in &self.type_decls {
            writeln!(f, "{tid} = type {tdecl}")?;
        }

        for (gid, gdecl) in &self.global_decls {
            writeln!(f, "{gid} = global {gdecl}")?;
        }

        for (gid, t) in &self.extern_decls {
            match t {
                Type::Fun(ts, rt) => writeln!(f, "declare {rt} {gid}({})", ts.iter().format(", "))?,
                _ => writeln!(f, "{gid} = external {t}")?,
            }
        }

        for func in &self.func_decls {
            writeln!(f, "{func}")?;
        }

        Ok(())
    }
}
