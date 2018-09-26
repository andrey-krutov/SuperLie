(*=======SuperLie.m====== Package for Lie Superalgebras =========== *)

(********** SubPackages *********)

DeclarePackage["SuperLie`Cartmatr`", {"CartanMatrixAlgebra", "CartanMatrix",
		 "RootReflection", "WeightToPolyGrade", "PolyGradeToWeight"}]

DeclarePackage["SuperLie`Deriv`", {"Der", "Der0", "der", "NDer", "ZDer", "ExteriorAlgebra"}]

DeclarePackage["SuperLie`Envsort`", {"EnvNormal", "EnvSortRule", "$EnvLess",
    "EnvelopingOperation", "EnvelopingSymbol", "ExpandOp", "ExpandOpRule",
    "dSortRule", "dNormal", "dSymbol", "CleardSymbol", "DiffAlgebra", "Dc"}]

DeclarePackage["SuperLie`Free`", {"FreeLieAlgebra" }]

DeclarePackage["SuperLie`Generate`", {"GenRel", "GenBasis", "GRange", "ToDegree"}]

DeclarePackage["SuperLie`Genvect`", {"GeneralSum", "GeneralSolve", "GeneralZero",
    "GeneralReduce", "GeneralPreImage", "GeneralBasis", "GeneralImage", "GeneralKernel",
    "GeneralInverseImage", "GeneralPlus", "GeneralDim", "GeneralAct", "GeneralIntersection"}]

DeclarePackage["SuperLie`Gl`", {"glAlgebra", "slAlgebra", "pslAlgebra" }]

DeclarePackage["SuperLie`Irrmod`", {"HWModule"}]

DeclarePackage["SuperLie`Poisson`", {"PoissonAlgebra", "Pb", "pb",
    "HamiltonAlgebra", "Hb", "hb",
    "ContactAlgebra", "Kb", "kb", "ButtinAlgebra", "Bb", "bb",
    "MoebiusAlgebra", "Mb", "mb", "OKAlgebra", "Ob", "ob",
    "RamondAlgebra", "Rb", "rb", "RamondD", "ZRamondD", "RamondK",
    "HamiltonianH", "\[CapitalDelta]", "EulerOp", "ContactK", "NewBrace" }]

DeclarePackage["SuperLie`Q`", {"qAlgebra", "sqAlgebra", "pqAlgebra",
    "psqAlgebra", "q2Algebra", "psq2Algebra", "psl2pAlgebra" }]

DeclarePackage["SuperLie`Space`", {"VectorSpace", "ReGrade", "TrivialSpace", "SpacePlus",
    "Relatives", "GetRelative", "NewRelative", "Mapping", "MappingRule",
    "MLeft", "CoLeft", "MRight", "CoRight", "PiRight", "DLeft",	"PiLeft", "DRight",
    "SubSpace", "Algebra", "CommutativeLieAlgebra", "Basis", "BasisPattern",
    "Image", "InSpace", "TheSpace", "TheAlgebra", "TheModule", (* "$Algebra", *)
    (*"$Module",*) "Components", "GList", "WList" }]

DeclarePackage["SuperLie`Subspace`", {"KerSpace", "GradedKerSpace"}]

DeclarePackage["SuperLie`Subalg`", {"SubAlgebra", "DefSubAlgebra", "AlgebraDecomposition"}]

DeclarePackage["SuperLie`Submod`", {"SubModule", "Ideal", "RestrictModule",
	"QuotientModule", "FactorModule", "QuotientAlgebra" }]

DeclarePackage["SuperLie`Symalg`", {"DegreeBasis", "UpToDegreeBasis",
	"GradeBasis", "FilterBasis"}]

DeclarePackage["SuperLie`Tensor`", {"MatrixLieAlgebra", "TensorSpace", "CompList", "Rank"}]

DeclarePackage["SuperLie`Vecfield`", {"VectorLieAlgebra", "VectorRepresentation",
	"Lb", "lb", "Div" }]

DeclarePackage["SuperLie`Vsplit`", {"SplitSum", "SplitList", "ForSplit", "AddSplit",
   "MergeSplit", "JoinSplit", "ApplySplit", "MapSplit", "PartSplit", "SkipVal"}]

(*DeclarePackage["SuperLie`Char`", {"FieldChar", "ModSolve", "DivPowers",
  "DivPowersQ", "UnDivPowers"}]*)

DeclarePackage["SuperLie`Solvars`", {"ParamAssume", "ParamSolve", "SolveSupportsPattern",
  "$ParamAssume"}]

DeclarePackage["SuperLie`Sparse`", {"ActToSparse", "SquaringToSparse", "FormToSparse",
  "PowerToSparse", "TestSparseBracket"}]

Off[General::shdw, Remove::rmnsm]
(* $osStart = "vect.osy" *)
BeginPackage["SuperLie`", {"SuperLie`Domain`", "SuperLie`Enum`"}]
dmn`ValuesList = {}
dmn`FlagsList = {Alpha, Scalar}

(* #################### PART 1. Domains #################### *)

SuperLie`STimesOp::usage = "STimesOp[domain] is the name of \"*\" in Scalar*domain."

SuperLie`PlusOp::usage = "PlusOp[domain] is the name of \"+\" in the domain."

SuperLie`CondOp::usage =
 "CondOp[domain] is the name of \"If\" operation with values in the domain.
CondOp[domain->name] defines this operation"

SuperLie`SumOp::usage =
 "SumOp[op] is the name of \"Sum\" function, associated with \"plus\"
operation op. SumOp[op->name] defines this operation."

SuperLie`PowerOp::usage =
 "PowerOp[op] is the name of \"power\" operation, associated with \"times\"
operation op. PowerOp[op->name] defines this operation."

(*
SuperLie`UnitElement::usage =
 "UnitElement[domain] is the \"1\" element in this domain"
*)

(* --------- Common Domain --------------- *)

SuperLie`GPlus::usage = "GPlus is the name of \"+\" in Common domain."
SuperLie`GTimes::usage = "GTimes is the name of \"*\" in Common domain."
SuperLie`GPower::usage = "GPower is the name of \"^\" in Common domain."
(* GSum::usage = "GSum is the name of Sum function in Common domain." *)

(* --------- Vector Domain --------------- *)

SuperLie`Vector::usage = 
 "Vector is the domain of vectors. Vector[obj,..] is the constructor of 
Vector objects."

SuperLie`UnVector::usage = "UnVector[obj,..] is the destructor of Vector objects."

SuperLie`VectorQ::usage =
  "VectorQ[x] returns True if x is an object of Vector domain."

SuperLie`VPlus::usage = "VPlus is the name of \"+\" in Vector domain."
SuperLie`VTimes::usage = "VTimes is the name of \"*\" in Vector domain."
SuperLie`VPower::usage = "VPower is the name of \"^\" in Vector domain."
SuperLie`VSum::usage = "VSum is the name of Sum function in Vector domain."
SuperLie`VIf::usage = "VIf[cond, v] is a vector-valued version of If function."
SuperLie`SVTimes::usage = "SVTimes is the name of \"*\" in Scalar*Vector."
SuperLie`tPower::usage = "v ^\[CircleTimes] n is the n-th tensor power of v."
(*SuperLie`ePower::usage = "v /\\^ n is the n-th exterior power of v."*)

SuperLie`VExpand::usage = SuperLie`VExpandRule::usage =
 "VExpand[expr] or expr //. VExpandRule expand out all VTimes and SVTimes
products in expr."

SuperLie`SVExpandRule::usage =
 "expr /. SVExpandRule expand out all scalar coefficients in SVTimes."

SuperLie`SVFactorRule::usage =
 "expr /. SVFactorRule factors all scalar coefficients in SVTimes."

SuperLie`SVSimplifyRule::usage =
 "expr /. SVSimplifyRule simplifies all scalar coefficients in SVTimes."

SuperLie`SVNormalRule::usage =
 "expr /. SVNormalRule converts all scalar coefficients in SVTimes to the
normal form using the function $SNormal."

SuperLie`VCollect::usage =
 "VCollect[expr] collects together terms c*v with the same v."

SuperLie`TCollect::usage =
 "TCollect[expr,case] collects together terms a**b with the same a (if case=First)
  or with same b (if case=Last). TCollect[expr,case,op] collect terms of operation
  op rather than **. The operation should not be declared additive or linear."

SuperLie`VNormal::usage =
 "VNormal[expr] returns the normal form of the vector expression."

SuperLie`SymmetricNormal::usage =
 "SymmetricNormal[expr] returns the normal form of the vector expression,
assuming the supersymmetry of vector product VTimes."

SuperLie`$SNormal::usage =
 "$SNormal is the user-defined function which is called by VNormal function
to convert the scalar coefficients to the normal form. Default is Together.
The function $SNormal must always convert to zero the scalars equal to zero."

SuperLie`VBasis::usage =
  "VBasis[expr] returns the list of vectors in the expression."

SuperLie`VSort::usage =
 "VSort[sum] sorts the terms of the vector sum in alphabetical order of
vectors."

SuperLie`VOrder::usage =
 "VOrder[v1,v2] returns 0,+1,-1 depending of order of vectors v1 and v2."

SuperLie`VOrderQ::usage =
 "VOrderQ[v1,v2] returns True or False depending of order of vectors v1 and v2."

SuperLie`VSameQ::usage = 
 "VSameQ[v1,v2] returns True if v1=c1*v, v2=c2*v with scalars c1, c2
and False otherwise."

SuperLie`SameElement::usage =
 "SameElement[v1,v2] returns True if the arguments represents the same element
of the basis of a vector space (maybe with differens scalar coefficients) and
False if they represent different elements.
If the arguments have symbolic indices, the function returns the condition of
equality of these indices e.g., SameElement[x[i],x[j]] returns i==j."

SuperLie`VSolve::usage =
 "VSolve[eqns, vars] attempts to solve an equation or set of equations for the
vector variables vars. VSolve[eqns] treats all vector variables encountered as
vars above. For other parameters and options see Solve."

SuperLie`SVSolve::usage =
 "SVSolve[eqns, vars] attempts to solve a vector equation or set of equations
for the scalar variables vars. SVSolve[eqns] treats all non-vector variables 
encountered as vars above. For other parameters and options see Solve."

SuperLie`ScalarEquation::usage =
 "ScalarEquation[equ] converts the equation with scalar variables to 
 scalar equation"

SuperLie`LinearChange::usage =
 "LinearChange[expr, rule] applies the rule or list of rules in an attempt to 
transform each vector in an expression expr."

SuperLie`$Solve::usage =
 "$Solve is the user-defined function for solving the scalar equations. The
default setting is $Solve = Solve."

SuperLie`$p::usage = "The value of $p is the characteristic of the base field"

(* ################### PART 2. Properties ################## *)

SuperLie`ZeroArg::usage = SuperLie`UnZeroArg::usage =
 "ZeroArg[f] is the property f[.., 0, ..] = 0."
SuperLie`ZeroArgRule::usage =
 "Use expr /. ZeroArgRule[f] to remove terms with f[..,0,..]."

(*
SuperLie`IdArg::usage = SuperLie`UnIdArg::usage =
 "IdArg[f] is the property f[x, Id, y] = f[x,y]."
SuperLie`IdArgRule::usage =
 "Use expr /. IdArgRule[f] to remove Id from f[..,Id,..]."
*)

SuperLie`Homogen::usage = SuperLie`UnHomogen::usage =
 "Homogen[f->deg] is the property f[c*v] = (c^deg)*f[v] for scalar c.
Homogen[f] is equivalent to Homogen[f->1]."
SuperLie`HomogenRule::usage = 
 "HomogenRule[f,deg] is replacement rule f[c*v] -> (c^deg)*f[v] where c is
scalar. Default value of deg is 1."

SuperLie`Symmetric::usage = SuperLie`UnSymmetric::usage = SuperLie`SymmetricQ::usage = 
 "Symmetric[f] is the property f[..,x,y,..] = (-1)^(P[x]P[y]) f[..,y,x,..]."
SuperLie`SymmetricRule::usage =
 "SymmetricRule[f] is the replacement rule for sorting the arguments of the
supercommutative function f."

SuperLie`SkewSymmetric::usage = SuperLie`UnSkewSymmetric::usage = SuperLie`SkewSymmetricQ::usage = 
 "SkewSymmetric[f] is the property
f[..,x,y,..] = (-1)^((1+P[x])(1+P[y])) f[..,y,x,..]."
SuperLie`SkewSymmetricRule::usage =
 "SkewSymmetricRule[f] is the replacement rule for sorting the arguments of the
superskewcommutative function f."

SuperLie`AntiSymmetric::usage = SuperLie`UnAntiSymmetric::usage = SuperLie`AntiSymmetricQ::usage = 
 "AntiSymmetric[f] is the property f[..,x,y,..] = - (-1)^(P[x]P[y]) f[..,y,x,..]."
SuperLie`AntiSymmetricRule::usage =
 "AntiSymmetricRule[f] is the replacement rule for sorting the arguments of the
superanticommutative function f."

SuperLie`AntiSkewSymmetric::usage = 
 "AntiSkewSymmetric[f] introduces the automatical sorting of operands of f using 
super-anti-skew simmetry f[..,x,y,..] = - (-1)^((1+P[x])(1+P[y])) f[..,y,x,..]."

SuperLie`UnAntiSkewSymmetric::usage = 
 "UnAntiSkewSymmetric[f] cancels the automatical sorting of operands of f."

SuperLie`AntiSkewSymmetricQ::usage = 
 "AntiSkewSymmetricQ[f] returns True if f was declared anti-skew-simmetric."

SuperLie`AntiSkewSymmetricRule::usage =
 "AntiSkewSymmetricRule[f] is the replacement rule for sorting the arguments of f
using super-anti-skew simmetry f[..,x,y,..] -> - (-1)^((1+P[x])(1+P[y])) f[..,y,x,..]."

SuperLie`Leibniz::usage = SuperLie`UnLeibniz::usage =
 "Leibniz[f->g] is the property  f @ g[x1,x2,..] = g[f@x1,x2,..] +/-
g[x1,f@x2,...] +/- ... (f acts as a derivation of parity P[f]).
Leibniz[f->{g1,..}] is the list if properties."

SuperLie`LeibnizRule::usage =
 "LeibnizRule[f, g] is the rule to expand  f[g[..]] into sum of
(+/-) g[.. f[.] ..] (like a derivation of parity P[f]).
LeibnizRule[f,{g1,..}] is the list of rules."

(*
SuperLie`LeibnizExpand::usage = 
 "LeibnizExpand[d[f[arg]],p] expands d[f[arg]] as a derivation of parity p."
*)

SuperLie`Jacobi::usage = SuperLie`UnJacobi::usage =
 "Jacobi[f->g] is the property  f[x, g[y1,y2,..]] = g[f[x,y1],y2,..] +/-
g[y1,f[x,y2],...] +/- ... (f acts as a bracket in Lie superalgebra).
Jacobi[f->{g1,..}] is the list if properties."

SuperLie`JacobiRule::usage =
 "JacobiRule[f, g] is the rule to expand  f[x, g[..]] into sum of
(+/-) g[.. f[x,.] ..] (like a bracket in Lie superalgebra).
JacobiRule[f,{g1,..}] is the list of rules."

SuperLie`Graded::usage = SuperLie`UnGraded::usage = SuperLie`GradedQ::usage =
 "Graded[op] is the property Grade[a ~op~ b] = Grade[a] + Grade[b]."

SuperLie`GradedPw::usage = SuperLie`UnGradedPw::usage = SuperLie`GradedPwQ::usage =
 "GradedPw[op] is the property Grade[a ~op~ k] = k*Grade[a]."

SuperLie`ThreadGraded::usage = SuperLie`UnThreadGraded::usage =
 "ThreadGraded[f] is the property f[a ~op~ b] = f[a] + f[b] for any
graded operation op. ThreadGraded[f->sm] is f[a ~op~ b] = f[a] ~sm~ f[b]."

SuperLie`ThreadGradedRule::usage =
 "ThreadGradedRule[f,sm] is the replacement rule f[a ~op~ b] -> f[a] ~sm~ f[b],
where op is any graded operation. Default sm is Plus."

SuperLie`DegTimes::usage = SuperLie`UnDegTimes::usage = 
 "DegTimes[op] is the property Deg[a ~op~ b, x] = Deg[a,x] + Deg[b,x]."

SuperLie`TestFirst::usage = SuperLie`UnTestFirst::usage =
 "TestFirst[f] is the property f[x1+...] = f[x1]."

SuperLie`TestFirstRule::usage =
 "TestFirstRule[f] is the replacement rule f[x1+...] -> f[x1]."

SuperLie`LogPower::usage = SuperLie`UnLogPower::usage =
 "LogPower[f] is the property f[x^p] = p*f[x]. LogPower[f->tms] is
f[x^p] = tm[p, f[x]]."

SuperLie`LogPowerPule::usage =
 "LogPowerRule[f, tm] is the replacement rule f[x^p] -> p ~tm~ f[x]. Default
tm is Scalar*Vector Times."

SuperLie`Additive::usage =
 "Additive[f] constitutes the property f[.., x+y, ..] = f[..,x,..] + f[..,y,..].
Additive[f->First] and Additive[f->Last] declares the additivity in the first
(last) argument of f."

SuperLie`UnAdditive::usage =
 "UnAdditive[f] cancels the additive expansion of f[.., x+y, ..].
UnAdditive[f->First] and UnAdditive[f->Last] cancel the additive expansion of the
first (last) argument of f."

SuperLie`AdditiveRule::usage =
 "AdditiveRule[f] is the replacement rule f[..,x+y,..] -> f[..,x,..] + f[..,y,..].
AdditiveRule[f,First] and Additive[f,Last] are rules for additive expansion of the
first (last) argument of f."

SuperLie`Linear::usage = SuperLie`UnLinear::usage = (* SuperLie`LinearQ::usage = *)
 "Linear[f] is the (multi)linearity of f."

SuperLie`LinearRule::usage =
 "LinearRule[f] is the list of rules for expand f[expr] if \"f\"
is linear function."

SuperLie`LinearCollectRule::usage =
 "LinearCollectRule[f] is the list of rules for collect together the term
in the sum f[x1,y1,..] + f[x2,y2,..]+...  wich differe in one argument only,
there f is linear function."

SuperLie`Output::usage = SuperLie`UnOutput::usage =
 "Output[v->f] defines the format of v[...] in OutputForm as f[v[...]].
The space constructor option Output->f defines the output format of the elements
of the space basis.
UnOutput[v] cancels the definition given by Output."  

SuperLie`TeX::usage = SuperLie`UnTeX::usage =
 "TeX[v->f] defines the format of v[...] in TeXForm as f[v[...]].
The space constructor option TeX->f defines the TeX output format of the elements
of the space basis.
UnTeX[v] cancels the definition given by TeX."

SuperLie`Standard::usage = SuperLie`UnStandard::usage =
 "Standard[v->f] defines the format of v[...] in StandardForm as f[v[...]].
The space constructor option Standard->f defines the Standard output format of the elements
of the space basis.
UnStandard[v] cancels the definition given by Standard."

SuperLie`Traditional::usage = SuperLie`UnTraditional::usage =
 "Traditional[v->f] defines the format of v[...] in TraditionalForm as f[v[...]].
The space constructor option Traditional->f defines the Traditional output format of the elements
of the space basis.
UnTraditional[v] cancels the definition given by Traditional."

(* ################## PART 3. Tools ###################### *)


SuperLie`MatchList::usage = 
  "MatchList[expr, ptrn] returns list of terms in \"expr\", matching the 
pattern \"ptrn\".\n MatchList[expr, ptrn, f] returns the list of values of
f[term].";

SuperLie`WithUnique::usage =
  "WithUnique[{symb..}, expr] evalutes expr replacing the listed symbols
with the new symbols with unique names." 

SuperLie`UniqueCounters::usage =
  "UniqueCounters[expr] return the expr with all counters in all sums and
tables replaced with unique symbols."


SuperLie`SimplifySignRule::usage =
  "SimplifySignRule is the rule for simplifying (-1)^expression."

SuperLie`SimplifySign::usage =
  "SimplifySign[expr] simplifies the (-1)^expo in the expr."

SuperLie`ArgForm::usage =
 "ArgForm[\"controlstring\"][expr] prints as the text of the
   controlstring, with the printed forms of the arguments of expr embedded."

SuperLie`SeqForm::usage =
 "SeqForm[e1,...][h[a1,..]] prints the sequence e1,..., substituting
   h, a1,... instead of placeholders #0, #1,... ."

(* #########  PART 4. Operations, Functions, Parameters ######### *)

SuperLie`FieldChar::usage =
"FieldChar[p] sets the characteristic of the base field, that may be zero or a prime number"

SuperLie`ModSolve::usage =
"ModSolve[eq, ...] solves scalar equations modulo $p (the characteristic of the base field).
The arguments are the same as for Solve"

SuperLie`DivPowers::usage = SuperLie`DivPowersQ::usage = SuperLie`UnDivPowers::usage =
"The property DivPowers[u] means that u^n and u[_]^n denote divided powers of u and u[_].
DivPowers[u->power] defines divided semantic for given \"power\" operation (e.g. exterior power)."

SuperLie`Dim::usage = "Dim[v] = dimension of the vector space v."
SuperLie`PDim::usage = "PDim[v] = {EvenDim,OddDim} is the dimension of the
vector superspace \"v\"."
SuperLie`FDim::usage = "FDim[v] returns dimension of the vector (super)space v
formatted  for output"

SuperLie`PList::usage = "PList[v] stores the list of parities of the element
of the basis of the vector space v."

SuperLie`P::usage = "P[vect] is the parity of vect."

SuperLie`Parity::usage = SuperLie`Mixed::usage =
  "Parity[vect] checks if vect is homogenious and returnt its parity.
For nonhomogenious vectors, and when checking fails, returns Mixed."

SuperLie`Plus2::usage = "Plus2[x,...] is a sum modulo 2"

SuperLie`Times2::usage = "Times2[x,...] is a product modulo 2"

SuperLie`Delta::usage = 
 "Delta[x,y] = 1 if x=y and =0 if x!=y; Delta[x] = Delta[x,0]."

SuperLie`Grade::usage = 
 "For graded object \"m\" value Grade[m[..]] is grading (degree)
of m[..]."

SuperLie`ToGrade::usage =
 "ToGrade->g is an optional parameter for space constructors. It restricts the
calculations to the range from -g to +g (the range of generators must be given).
ToGrade[m] returns this limit. The results of operations in m are evaluated
only if its grade is berweein -ToGrade[m] and +ToGrade[m]."

SuperLie`Weight::usage = "Weight[v] is the weight of the homogeneous element \"v\"."

SuperLie`WeightMark::usage = "WeightMark[length, mark, ...] returns a list of given
length. All elements of the result are initially set to 0.
For every mark mi, if mi>0, the mi-th element of the result is increased by 1.
If mi<0, the (-mi)-th element is diminished by 1."

SuperLie`PolyGrade::usage = "PolyGrade[v] - weight range - is the weight of v in the 
basis of primitive roots."

SuperLie`NewBracket::usage =
  "NewBracket[op] defines op as the bracket in Lie superalgebra.
The options Parity and Grade declare the parity and the grade of the bracket"

SuperLie`Bracket::usage =
 "Bracket[alg] is the name of the bracket operation in the Lie algebra."

SuperLie`bracket::usage =
 "bracket[alg] is the name of unevaluated form of the bracket in Lie algebra."

SuperLie`BracketMode::usage = SuperLie`Regular::usage = SuperLie`Tabular::usage =
 "BracketMode[md] is the method of the definition of the bracket operation
on the algebra or of the action of the algebra on the module. The value
of BracketMode[md] can be Regular or Tabular."

SuperLie`Operator::usage =
 "If symb denotes the passive form of some operatot, Operator[symb] returns the name
of the active form of the same operator."

SuperLie`OpSymbol::usage =
 "If symb denotes the active form of some operatot, OpSymbol[symb] returns the name
of the passive form of the same operator."

SuperLie`Act::usage = "Act[g,m] - the action of the element \"g\" on  \"m\"."

SuperLie`act::usage = 
 "act[g,m] - the action of the element  \"g\" on  \"m\" (unevaluated)."

SuperLie`ActTable::usage =
 "ActTable[g] is the table used to define the bracket on algebra g
if BracketMode[g] is Tabular. ActTable[g,m] is used to define the
action of g on m."

SuperLie`Squaring::usage =
 "2*Squaring[x,bracket] = bracket[x,x] for odd x. This operation is defined independently
of the bracket so it is defined even for fields with characteristic 2."

SuperLie`SqrTable::usage =
 "SqrTable[g] is the table used to define the squaring on algebra g
if BracketMode[g] is Tabular."

SuperLie`Deg::usage =
 "Deg[times[...], x] is the degree of \"x\" in expression \"times[...]\"."

SuperLie`LDer::usage =
 "LDer[expr, x, ptrn] is the left partial derivative of expression expr.
The pattern ptrn should match all independent and none dependent variables."

SuperLie`ZLDer::usage =
 "ZLDer[x,ptrn][expr] is the left partial derivative of expression expr.
The pattern ptrn should match all independent and none dependent variables.
ZLDer[x,ptrn] may be used in symbolic calculations."

SuperLie`RDer::usage =
 "RDer[expr, x, ptrn] is the right partial derivative of expression expr.
The pattern ptrn should match all independent and none dependent variables."

SuperLie`ZRDer::usage =
 "ZRDer[x,ptrn][expr] is the right partial derivative of expression expr.
The pattern ptrn should match all independent and none dependent variables.
ZRDer[x,ptrn] may be used in symbolic calculations."

CircleTimes::usage = "v1 \[CircleTimes] v2 ...  is the tensor product of the vectors."

Wedge::usage = "v1\[Wedge]v2\[Wedge]... is the exterior product of the vectors."

SuperLie`wPower::usage = "\!\(v\^\(\[Wedge]n\)\" is the n-th exterior power of vector v\"\)"

SuperLie`wedge::usage = "wedge[e1,...,en] is the internal representation of the basis of
exterior algebras. The external representation is e1\[Wedge]...\[Wedge]en."

SuperLie`Tp::usage = 
  "expr1 ** expr2 ** ...  is the tensor product of expressions."
(* SuperLie`up::usage = "\"up\" is the multiplication in the enveloping algebra." *)

(* SuperLie`Id::usage = "Id is the unit element in tensor algebra" *)

SuperLie`ZId::usage = "ZId is the identity operator. Used in symbolical calculations."

SuperLie`Auto::usage = "Auto is the default value for some options"

SuperLie`CTimes::usage =
 "CTimes[op] declares new \"Coefficient Times\" operation that may be used instead of **
between coefficient and vector parts of forms, vector fields, etc.
CTimes->op is an options that indicates such operation." 
 
(* ########### PART 5. Space Constructors ############## *)

SuperLie`DecompositionList::usage =
 "DecompositionList[g,f] returns the list of subalgebras in the decomposition
 f of the algeba g."

SuperLie`DecompositionRule::usage =
 "expr /. DecompositionRule[g,f] replaces the elements of the basis of g in
 the expression expr with their images under decomposition f."

SuperLie`CartanTriade::usage =
 "CartanTriade is the decomposition of algebras in 3 subalgebras:
  g -> {g+, g0, g-} (the components of positive, null and negative weight)"

SuperLie`NGen::usage = "NGen[g] is the number of generators of the \"g\""


(*SuperLie`UEBasis::usage =
 "UEBasis[alg] builds a graded basis of the Enveloping Algebra of the
given graded algebra \"alg\"."*)


Unprotect[General]

General::novect = "`` is not a vector. Replaced with 0."
General::novl = "`` is not vector or list of vectors."

Protect[General]

(* ---------  Debug tools -------------- *)

SuperLie`$DPrint::usage = SuperLie`DPrint::usage = 
  "DPrint[level, data...] prints data (using Print) if $DPrint>=level."

SuperLie`$DPrintLabel::usage =
  "The value of $DPrintLabel[] is printed as a label for debug printing.
Use $DPrintLabel=DateString or TimeString to use [date and] time as label.
Use $DPrintLabel=None for debug printing without labels."

If [$VersionNumber < 6,
  DateString::usage =
    "DateString[] return a string representing the current date and time."]

SuperLie`TimeString::usage =
  "TimeString[] return a string representing the current time."


Begin["$`"] (* =============================== Private ========== *)

(*
VariantFirst[def_, var_] :=
  With[{hdef=HoldPattern[def], hvar=HoldPattern[var]},
    With[{head=hdef[[1,0]]},
	 With[{rule=Select[DownValues[head], #[[1]]===hdef&][[1]]},
	   Append[ DownValues[head],
		rule /.
		  {Verbatim[hdef] ->hvar,
		   All->First,
		   f_[Verbatim[$`x___],rest___]:>f[rest],
		   f_[$`x,rest___]:>f[rest]}]]]]
*)

(* -----------  PROPERTY : ZeroArg ------------ *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  ZeroArgRule[f_] :=   ( wrapper[f[x___, 0, y___]] -> 0 );
  ZeroArgRule[f_, First] :=   ( wrapper[f[0, y___]] -> 0 );
  ZeroArgRule[f_, Last] :=   ( wrapper[f[x___, 0]] -> 0 );
]
NewProperty[ ZeroArg, {Rule} ]

(* -----------  PROPERTY : IdArg ------------ *)
(*
With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  IdArgRule[f_] :=   ( wrapper[f[x___, Id, y___]] :> f[x,y] )]

NewProperty[ IdArg, {Rule} ]
*)

(* ----------- PROPERTY : Homogen ------------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 HomogenRule[f_,First,deg_:1] :=
  {With[ {times = STimesOp[Domain[f]]},
     Switch[deg,
	1, wrapper[f[SVTimes[c_,v_], y___]] :> c ~times~ f[v,y],
	0, wrapper[f[(SVTimes|VIf)[c_,v_], y___]] :> f[v,y],
	_, wrapper[f[SVTimes[c_,v_], y___]] :> (c^deg) ~times~ f[v,y]
   ] ],
   With[ {if = CondOp[Domain[f]]},
     If[if=!=None && deg=!=0,
 	wrapper[f[VIf[c_,v_], y___]] :> if[c, f[v,y]],
	(*else*) Unevaluated[]
   ] ]
 };
 HomogenRule[f_,Last,deg_:1] :=
  {With[ {times = STimesOp[Domain[f]]},
     Switch[deg,
	1, wrapper[f[x___, SVTimes[c_,v_]]] :> c ~times~ f[x,v],
	0, wrapper[f[x___, (SVTimes|VIf)[c_,v_]]] :> f[x,v],
	_, wrapper[f[x___, SVTimes[c_,v_]]] :> (c^deg) ~times~ f[x,v]
   ] ],
   With[ {if = CondOp[Domain[f]]},
     If[if=!=None && deg=!=0,
 	wrapper[f[x___, VIf[c_,v_]]] :> if[c, f[x,v]],
	(*else*) Unevaluated[]
   ] ]
 };
 HomogenRule[f_,{arg___}] := HomogenRule[f,arg];
 HomogenRule[f_,deg_:1] :=
  {With[ {times = STimesOp[Domain[f]]},
     Switch[deg,
	1, wrapper[f[x___, SVTimes[c_,v_], y___]] :> c ~times~ f[x,v,y],
	0, wrapper[f[x___, (SVTimes|VIf)[c_,v_], y___]] :> f[x,v,y],
	_, wrapper[f[x___, SVTimes[c_,v_], y___]] :> (c^deg) ~times~ f[x,v,y]
   ] ],
   With[ {if = CondOp[Domain[f]]},
     If[if=!=None && deg=!=0,
	    wrapper[f[x___, VIf[c_,v_], y___]] :> if[c, f[x,v,y]],
	(*else*) Unevaluated[]
   ] ]
 }
]

HomogenPowerOp[f_,deg_:1] := With[ {pw = PowerOp[f]}, If[pw=!=None, HomogenPower[pw->deg]]]
UnHomogenPowerOp[f_,deg_:1] := With[ {pw = PowerOp[f]}, If[pw=!=None, UnHomogenPower[pw->deg]]]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  HomogenPowerRule[pw_,deg_:1] :=
    With[ {times = STimesOp[Domain[pw]]},
        wrapper[pw[times[c_,v_], n_]] :> times[Power[c,n*deg], pw[v,n]]]]


NewProperty[Homogen, {Rule, Also->HomogenPowerOp}]
NewProperty[HomogenPower, {Rule}]


(* ------------ PROPERTIES : Symmetric, SkewSymmetric ------------ *)

SymmetricRule[op_] = genSymmetricRule[op,1,0]
SkewSymmetricRule[op_] = genSymmetricRule[op,1,1]
AntiSymmetricRule[op_] = genSymmetricRule[op,-1,0]
AntiSkewSymmetricRule[op_] = genSymmetricRule[op,-1,1]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 genSymmetricRule[op_,sign_,skew_] := 
  With[{pw = PowerOp[op], stimes=STimesOp[Domain[op]],
        asym=If[sign>0, 1-skew,skew]},
   If [pw===None,
    { wrapper[ op[args___ /; !OrderedQ[{args}]] ] :>
	(SuperSignature[{args}, sign, skew] //. SimplifySignRule) ~stimes~
		 Sort[Unevaluated[op[args]]],
      wrapper[op[___, x_/;P[x]==asym, x_, ___]] :> 0
    },
  (*else*)
     With [{ord = OrderedQ[#/.pw[a_,_]:>a]&},
      { wrapper[ op[args___ /; !ord[{args}]] ] :> 
	   (SuperSignature[{args}, sign, skew, ord] //. SimplifySignRule) 
		~stimes~ Sort[Unevaluated[op[args]],ord[{#1,#2}]&],
	  wrapper[ (x_/;P[x]==asym)~pw~(n_/;n!=1&&n!=-1)] :> 0
      } ]
  ]
 ]
]

Attributes[SuperSignature] = {HoldFirst}


SuperSignature[arg_,sign_,skew_,ord_:OrderedQ] :=
 Block[{ssgn=1, pplist},
    pplist = P /@ arg;
    If [skew=!=0, pplist = 1 - pplist];
    Do [If [!ord[arg[[{i,j}]]],
	    ssgn *= sign*(-1)^(pplist[[i]]*pplist[[j]])],
	{j,2,Length[pplist]}, {i, j-1}
    ];
 ssgn
 ]
   
NewProperty[Symmetric, {Rule,Flag}]
NewProperty[SkewSymmetric, {Rule,Flag}]
NewProperty[AntiSymmetric, {Rule,Flag}]
NewProperty[AntiSkewSymmetric, {Rule,Flag}]

Symmetric[v_] := True /;
  Which[SkewSymmetricQ[v], UnSkewSymmetric[v]; False,
        AntiSymmetricQ[v], UnAntiSymmetric[v]; False,
        AntiSkewSymmetricQ[v], UnAntiSkewSymmetric[v]; False,
        SymmetricQ[v], True,
        True, False]
        
AntiSymmetric[v_] := True /;
  Which[SkewSymmetricQ[v], UnSkewSymmetric[v]; False,
        AntiSymmetricQ[v], True,
        AntiSkewSymmetricQ[v], UnAntiSkewSymmetric[v]; False,
        SymmetricQ[v], UnSymmetric[v]; False,
        True, False]

SkewSymmetric[v_] := True /;
  Which[SkewSymmetricQ[v], True,
        AntiSymmetricQ[v], UnAntiSymmetric[v]; False,
        AntiSkewSymmetricQ[v], UnAntiSkewSymmetric[v]; False,
        SymmetricQ[v], UnSymmetric[v]; False,
        True, False]

AntiSkewSymmetric[v_] := True /;
  Which[SkewSymmetricQ[v], UnSkewSymmetric[v]; False,
        AntiSymmetricQ[v], UnAntiSymmetric[v]; False,
        AntiSkewSymmetricQ[v], True,
        SymmetricQ[v], UnSymmetric[v]; False,
        True, False]

(* ------------------ PowerOp -------------------- *)

PowerOp[_] = None;

PowerOp[op_->powerop_] :=
( PowerOp[op] ^= powerop;
  powerop/: Domain[powerop, First] = Domain[powerop] ^= Domain[op];
  powerop/: Domain[powerop, Last] = Scalar;
  Default[powerop, 2] := 1;
  Attributes[powerop] = {Listable, OneIdentity};
  powerop[x_,0] := Evaluate[ op[] ];
  powerop[x_,1] := x;
  powerop[powerop[x_,k_],l_] :=  (* the outer power is NEVER divided *)
    If[DivPowersQ[x,powerop],
       SVTimes[Product[Binomial[i*k,k],{i,l}], powerop[x, k*l]],
       powerop[x, k*l]];
  If [op=!=Wedge,
    op[y___,x_~powerop~(n1_.), x_~powerop~(n2_.),z___] :=
       If[DivPowersQ[x,powerop],
          Binomial[n1+n2,n1] ~SVTimes~ op[y,x~powerop~(n1+n2),z],
	  op[y,x~powerop~(n1+n2),z]]];
  powerop[op[],n_] := op[];
  powerop[0,n_/;n>0] := 0;
  If[DegTimesQ[op], DegPowerQ[powerop]^=True];
  If[GradedQ[op], GradedPwQ[powerop]^=True];
  P[powerop[x_, n_]] ^:= PolynomialMod[P[x]*n, 2];
  With[{asym=Which[SymmetricQ[op]||AntiSkewSymmetricQ[op], 1,
                   AntiSymmetricQ[op]||SkewSymmetricQ[op], 0]},
    If[NumberQ[asym],
      (x_/;P[x]==asym)~powerop~(n_/;n!=1&&n!=-1) := 0]]
)

NewValue[PowerOp];

PolyPattern[times_, ptrn_]:=
  With[{power=PowerOp[times]},
    If [power===None, 
      ptrn|times[ptrn...],
      power[ptrn,_.] | times[(power[ptrn,_.])...]
    ]]



(* ------------------ SumOp -------------------- *)

SumOp[_] = None;

SumOp[op_->sumop_] :=
( SumOp[op] ^= sumop;
  Attributes[sumop] = {HoldAll,OneIdentity};
  SetProperties[sumop, {Domain[op], Domain[op]->First, ZeroArg->First}];
  sumop[f_] := Unevaluated[f];
  sumop[f_, it1___,iter:{_,bnd__/;(NumberQ/@Unevaluated[And[bnd]])},it2___] :=
		sumop[ Evaluate[op @@ Table[sumop[f, it2],iter], it1]];
  sumop[f_,it1___,{i_,from_->to_},it2___] :=
    With [{diff = Expand[to-from]},
      Which [ TrueQ[diff>0],
		Evaluate[sumop[f, it1, Evaluate[{i,from,to-1}],it2]],
	      TrueQ[diff<0], 
		Evaluate[STimesOp[Domain[op]] [-1,
				  sumop[f, it1, Evaluate[{i,to,from-1}],it2]]],
	      TrueQ[diff==0],	0
      ] /; NumberQ[diff]
    ]
)

NewValue[SumOp];

(* ------------------ CondOp -------------------- *)

CondOp[_] = None;

CondOp[dmn_->if_] :=
( CondOp[dmn] ^= if;
  Attributes[if] = {HoldRest};
  SetProperties[if, {dmn, dmn->Last, ZeroArg->Last}];
  if[True, v_] := v;
  if[False, _] = 0;
  Default[if, 1] ^= True;
)

NewValue[CondOp];


(* ---------- PROPERTIES : Leibniz and Jacobi ------------- *)

Leibniz::par = "No parity of `` defined. Assumed 0."

LeibnizExpandPower[f_[prm___,power_[v_,n_]], times_] :=
 If[DivPowersQ[v,power],
    f[prm,v] ~times~ power[v,n-1],
    n ~SVTimes~ (f[prm,v] ~times~ power[v,n-1])]


LeibnizExpand[ f_[prm___,expr_], par_ ] := 
  Module [{ m, fm, s=1, s1, ph=P[Head[expr]] },
    If[!NumberQ[ph],
      Message[Leibniz::par, Head[expr]];
      ph = 0];
    VPlus @@ Table[
      m = expr[[i]];
      s1 = s;
      s *= (-1)^(par~Times~(P[m]+ph));
      If [(fm = f[prm,m])===0, 0,
	 (*else*) s1 ~SVTimes~ ReplacePart[expr, fm, i]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]

LeibnizExpand[ f_[prm___,expr_], 0 ] := 
  Module [{ m, fm },
    VPlus @@ Table[
      m = expr[[i]];
      If [(fm = f[prm,m])===0, 0,
	 (*else*) ReplacePart[expr, fm, i]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]


Attributes[LeibnizRule] = {Listable}

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 LeibnizRule[f_, g_] :=
 { wrapper[f[expr_g]] :> LeibnizExpand[Unevaluated[f[expr]], P[f]], 
   With[{power=PowerOp[g]},
	If [power===None, Unevaluated[],
	(*else*) wrapper[f[expr_power]] :>
		LeibnizExpandPower[ Unevaluated[f[expr]], g ]
	]
   ]
 };
 JacobiRule[f_, g_] :=
  { With[{pf=P[f], fn=LeibnizExpandFn[g]},
      Which[
        !NumberQ[pf],
          Message[Leibniz::par, f];
	      wrapper[f[any_, expr_g]] :> fn[Unevaluated[f[any,expr]], P[any]],
		pf===0,
          wrapper[f[any_, expr_g]] :> fn[Unevaluated[f[any,expr]], P[any]],
		True,
          wrapper[f[any_, expr_g]] :> fn[Unevaluated[f[any,expr]], P[any]+pf]]],
    With[{power=PowerOp[g]},
	  If [power===None,
	    Unevaluated[],
	  (*else*)
	    wrapper[f[any_, expr_power]] :>
	      LeibnizExpandPower[ Unevaluated[f[any, expr]], g ]
	]
   ]
  }
]

LeibnizExpandFn[_] = LeibnizExpand

LeibnizRule[f_, g_List] := Join @@ (LeibnizRule[f, #]& /@ g)

JacobiRule[f_, g_List] := Join @@ (JacobiRule[f, #]& /@ g)


NewProperty[ Leibniz, {Rule} ]
(*NewProperty[ Jacobi, {TagRule} ]*)

Jacobi[fn_->op_] :=
  (AutoRule[Unevaluated[JacobiRule[fn,op][[1]]], op];
   With[{power=PowerOp[op]},
     If [power=!=None,
	AutoRule[Unevaluated[JacobiRule[fn,op][[2]]], power]]];
   Rules[fn] ^= Union[Rules[fn], {HoldForm[JacobiRule[fn,op]]}])

Jacobi[fn_->op_List] := (Jacobi[fn->#]& /@ op; Rules[fn])

UnJacobi[fn_->op_] :=
 (UnAutoRule[JacobiRule[fn,op][[1]]];
  With[{power=PowerOp[op]},
    If [power=!=None,UnAutoRule[JacobiRule[fn,op][[2]]]]];
  Rules[fn] ^= Complement[Rules[fn], {HoldForm[JacobiRule[fn,op]]}])

UnJacobi[fn_->op_List] := (UnJacobi[fn->#]& /@ op; Rules[fn])

(* ---- PROPERTIES : Graded, ThreadGraded, TestFirst, LogPower ---- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 ThreadGradedRule[func_, add_] :=
   wrapper[func[(hd_?GradedQ)[ff___]]] :> func /@ Unevaluated[add[ff]];
 ThreadGradedRule[func_] :=
   With[{add=PlusOp[Domain[func]],times=STimesOp[Domain[func]]},
    {wrapper[func[(hd_?GradedQ)[ff___]]] :> func /@ Unevaluated[add[ff]],
     wrapper[func[(hd_?GradedPwQ)[e_,n_]]] :> times[n,func[e]]}];
 TestFirstRule[func_] :=
   wrapper[func[expr_VPlus]] :> func[First[expr]];
 LogPowerRule[func_, times_] :=
   wrapper[func[VPower[x_,p_]]] :> p ~times~ func[x];
 LogPowerRule[func_] :=
   wrapper[func[VPower[x_,p_]]] :> p ~(TimesOp[Domain[func]])~ func[x]
]

NewProperty[Graded]
NewProperty[GradedPw]
NewProperty[ThreadGraded, {Rule} ]
NewProperty[TestFirst, {Rule}]
NewProperty[LogPower, {Rule}]

DegTimes[op_]:=
 (DegTimesQ[op]^=True;
  With[{pw=PowerOp[op]},If[pw=!=None,DegPowerQ[pw]^=True]];
 )

DegTimes[op_, ops__] := Scan[DegTimes, {op, ops}]

UnDegTimes[op_]:=
 (op/:DegTimesQ[op]=.;
  With[{pw=PowerOp[op]},If[pw=!=None,pw/:DegPowerQ[pw]=.]];
 )

UnDegTimes[op_, ops__] := Scan[UnDegTimes, {op, ops}]

(* ============  DOMAIN : Scalar =============== *)

tmp$ = Unprotect[Plus, Times, Power, Expand, Sum, DirectedInfinity]

Operation[ Plus, GPlus[Scalar..]->Scalar ]
Operation[ Times, GTimes[Scalar..]->Scalar ]
Operation[ Power, GPower[Scalar, Scalar]->Scalar ]

(*UnitElement[Scalar] ^= 1;*)
STimesOp[Scalar] ^= Times
PlusOp[Scalar] ^= Plus
PowerOp[Times] ^= Power
SumOp[Plus] ^= Sum
Scalar[Sum]
CondOp[Scalar] ^= If
ScalarQ[DirectedInfinity] ^= True

Sum[f_, {i_,v_/;!NumberQ[v],n_Integer}, iter___] := - Sum[f,{i,n,v},iter]
Sum[f_,{i_,from_->to_},iter___] :=
   With [{diff = Expand[to-from]},
      Which [ TrueQ[diff>0], 	Sum[f,{i,from,to-1},iter],
	      TrueQ[diff<0],  - Sum[f,{i,to,from-1},iter],
	      TrueQ[diff==0],	0,
	      NumberQ[from],	Sum[f,{i,from,to-1},iter],
	      NumberQ[to],    - Sum[f,{i,to,from-1},iter],
	      True,	Sum[f,{i,to-1},iter] - Sum[f,{i,from-1},iter]
   ]  ]

Plus/:Literal[f_Plus[x___]] := TryApply[#,x]&/@Unevaluated[f]
Times/:Literal[f_Times[x___]] := TryApply[#,x]&/@Unevaluated[f]
Power/:Literal[(f_^n_)[x___]] := f[x]^n

TryApply[f_,x___]:=
  Which[
    NumberQ[f], f,
    SymbolQ[f], If[HasSVargs[f], f[x], f],
    Head[f]===Plus || Head[f]===Times , TryApply[#,x]&/@Unevaluated[f],
    Head[f]===Power, TryApply[First[f],x]^Second[f],
    True, f];

HasSVargs[f_] :=
 Module[{dmn},
   {} =!= Intersection[
     MatchList[UpValues[f] /. Domain -> dmn, dmn[f, __]] /. dmn -> Domain,
     {Scalar, Vector}]]

(* Needs["Algebra`SymbolicSum`"] *)

(* ============ DOMAIN : Vector ================ *)

NewDomain[Vector, {Flag}, "V"]

Operation[ VPlus,   GPlus[Vector..]->Vector ]
Operation[ VTimes,  GTimes[Vector..]->Vector ]
(*Operation[ SVTimes, GTimes[Scalar..->Times, Vector]->Vector]*)
(*Operation[ SVTimes, GTimes[Scalar..->Times, Vector..->VTimes]->Vector]*)
P[VTimes] ^= 0

GTimes[x__?(ScalarQ[#]||VectorQ[#]&)] :=
  SVTimes[Select[Unevaluated[Times[x]], ScalarQ],
	  Select[Unevaluated[VTimes[x]], VectorQ]]

Operation[ VPower,  GPower[Vector, Scalar]->Vector ]

(*UnitElement[Vector] ^= Id*)
Default[VPlus] := 0
Default[SVTimes] := 1
(*Default[VTimes] := Id*)

STimesOp[Vector] ^= SVTimes
PlusOp[Vector] ^= VPlus
SumOp[VPlus->VSum]
CondOp[Vector->VIf]

VPlus[x___, 0, y___] := VPlus[x,y]
VPlus[] = 0
VPlus[x_] := Unevaluated[x]
VTimes[x_] := Unevaluated[x]
Vector[SVTimes]
SVTimes[1, y_] := y
SVTimes[x_, 1] := x
SVTimes[0, _] := 0
SVTimes[_, 0] := 0
SVTimes[x_, SVTimes[y_, z_]] := SVTimes[x~Times~y, z]
SVTimes/: Domain[SVTimes,First] = Scalar
SVTimes/: Domain[SVTimes,Last] = Vector
VTimes/: Domain[VTimes,_] = Vector

SVTimes/: InverseFunction[SVTimes, 2, 2] := SVTimes[1/#1, #2] &
VPlus/: InverseFunction[VPlus, no_, _] := 
	SVTimes[-1, VPlus @@ MapAt[ SVTimes[-1,#1]&, {##}, no ] ]&

VPlus/:Literal[VPlus[f___][x___]]:=#[x]&/@Unevaluated[VPlus[f]]
SVTimes/:Literal[SVTimes[c_,f_][x___]]:=SVTimes[c,f[x]]
VSum/:Literal[VSum[f_,iter___][x___]]:=VSum[f[x],iter]
VIf/:Literal[VIf[cond_,f_][x___]]:=VIf[cond,f[x]]
VTimes/:Literal[VTimes[v__,f_][x_]]:=VTimes[v,f[x]]


Attributes[VPlus] = {Flat, Listable, OneIdentity}
Attributes[VPower] = {Listable, OneIdentity}
SetProperties[VTimes, {PowerOp->VPower, ZeroArg, (*IdArg,*) Homogen,
	Graded, DegTimes (*, Symmetric*) } ]
Attributes[VTimes] = {Flat, Listable, OneIdentity}
Attributes[SVTimes] = {Listable, OneIdentity}

(* ------------------- VBasis -------------------------- *)

VBasis[0] = {}
VBasis[True] = {}
VBasis[False] = {}
VBasis[x_/;AtomQ[x]] := { If [VectorQ[x], x, Message[VBasis::novect, x]; 1] }
VBasis[SVTimes[c_, v_]] := VBasis[v]
VBasis[(h_ /; VectorQ[h] && h =!= VPlus)[i___]] := {h[i]}
VBasis[expr_] := Union @ Flatten [ VBasis /@ List @@ expr ]

(* -------------------- VSolve -------------------------- #)
>  Solves the equation with vector variables
(# ------------------------------------------------------ *)

$Solve = Solve

VSolve[equ_, vars_List, args___] :=
  With[{encode = MapIndexed[#1->$`$sol$[First[#2]]&, vars],
	decode = MapIndexed[$`$sol$[First[#2]]->#1&, vars],
	n=Length[vars]},
  $Solve[LinearChange[equ, encode] /. { SVTimes->Times, VPlus->Plus}, 
          Array[$`$sol$, n], args] /.decode //. RestoreSV]

VSolve[equ_, var_, args___] := VSolve[equ, {var}, args]

VSolve[equ_] := VSolve[equ, VBasis[equ]]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 RestoreSV =
  { wrapper[e_Plus] :> VPlus@@e /; VectorQ[e[[1]]],
    wrapper[(c__?ScalarQ) * (v_?VectorQ)] :> SVTimes[Times[c], v]
  }
]

(* -------------------- SVSolve ------------------------- #)
>  Solves equation with scalar variables and vector coefficients
(# ------------------------------------------------------ *)

SVSolve[equ_, other___] := $Solve[ ScalarEquation[equ], other ]
SVSolve[True, other___] := {{}}
SVSolve[False, other___] := {}

(* ------------------- ScalarEquation ------------------- #)
>  Convert the equation with scalar variables to scalar equation
(# ------------------------------------------------------ *)

(*
ScalarEquation[equ_] :=
  With[{v = VBasis[equ]},
    Flatten @ Table[equ /. v[[i]]->1 /.
		{VPlus->Plus,SVTimes->Times} /. _?VectorQ->0,
	  {i,Length[v]}
  ] ]
*)

ScalarEquation[a_==b_] := 
  With[{e = VPlus[a, SVTimes[-1, b]] //. VExpandRule},
    SEq /@ Split[Sort[VPlusTerms[e], VOrderQ], VSameQ]]

VPlusTerms[e_VPlus] := List @@ e
VPlusTerms[e_] := {e}

SEq[e_] := ($SNormal[Plus @@ SVCoef /@ e]==0)

ScalarEquation[eq_List] := Flatten[ScalarEquation/@eq]

ScalarEquation[True] = True
ScalarEquation[False] = False

(* ----------------- LinearChange ---------------------- *)

(*
SuperLie`Replace[f_, r:(_Rule|_RuleDelayed|_Dispatch)] := System`Replace[f,r]
SuperLie`Replace[f_, r_List] := First @ System`Replace[{f}, Map[List,r,{2}]]
*)

LinearChange[e:(_List|_VPlus|_Rule|_RuleDelayed|_Equal|_Unequal), rule_] := 
		(LinearChange[#,rule]& /@ Unevaluated[e])

LinearChange[(h:SVTimes|VIf)[c_, v_], rule_] := h[c, LinearChange[v, rule]]
LinearChange[VSum[v_, iter_], rule_] := VSum[LinearChange[v, rule],iter]
LinearChange[v_/;VectorQ[v], rule_] := Replace[v,rule]
LinearChange[0, _] = 0
LinearChange[v_, rule_] := (Message[LinearChange::novect, v];0)

(* --------------- Symbolic Manipulations --------------------- *)

VExpand[expr_] := expr //. VExpandRule

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 VExpandRule =
 { wrapper[VTimes[x___,y_VPlus, z___]] :> (VTimes[x, #, z]& /@ y),
   wrapper[SVTimes[x_, y_VPlus]] :> (SVTimes[x, # ]& /@ y),
   wrapper[VPower[SVTimes[c_,v_], n_]] :> (c^n) ~SVTimes~ VPower[v,n],
   wrapper[VPower[x_VTimes, n_/;n>1]] :>
	VTimes @@ Table[Sequence@@x, {n}],
   wrapper[VPower[x_VPlus,n_Integer]] :>
     If[SymmetricQ[VTimes] && TrueQ[ExDivPowersQ[x]],
        ExpandDivPower[x, n],
	(VTimes[VPower[x,n-1],#]& /@ x)] /; n>1
 };
 SVNormalRule = wrapper[c_~SVTimes~v_] :> $SNormal[c]~SVTimes~v
]

$SNormal = Together

(* ------- VNormal ------ *)

VNormal[expr_] := VCollect[expr //. VExpandRule] /. SVNormalRule

SymmetricNormal[expr_] :=
   VCollect[expr //. VExpandRule //. SymmetricRule[VTimes]] /. SVNormalRule

VCollect[expr_List] := VCollect /@ expr

VCollect[VSum[f_, iter__]] := VSum[VCollect[f], iter]

VCollect[e_VPlus] := 
  VPlus @@ SVMerge /@ Split[Sort[List@@e, VOrderQ], VSameQ]

VCollect[e_]:=e

SVMerge[e_] := 
  SVTimes[Plus @@ SVCoef /@ e, SVVect[e[[1]]] ]

SVCoef[SVTimes[c_,_]] := c
SVCoef[v_] := 1

SVVect[SVTimes[_.,v_]] := v


TCollect[ex_VPlus, case_, op_:NonCommutativeMultiply]:=
  Block[{tcolOp=op,tcolCase=case},
    With[{e=ex/.Switch[tcolCase,
                 Last, SVTimes[c_, tcolOp[x_, y__]] :> tcolOp[SVTimes[c, x], y],
                 First, SVTimes[c_, tcolOp[x__, y_]] :> tcolOp[x, SVTimes[c, y]],
                 _, Message[TCollect::arg, case]; Return[$Failed]]},
      VPlus @@ TMerge /@ Split[Sort[List@@e, TOrderQ], TSameQ]]]

TMerge[e_] :=
  Switch[tcolCase,
    Last, tcolOp[ VPlus@@First/@e, e[[1,2]] ],
    First,  tcolOp[ e[[1,1]], VPlus@@Last/@e ]]

TOrderQ[x_,y_] := VOrderQ[tcolCase[x],tcolCase[y]]
TSameQ[x_,y_] := VSameQ[tcolCase[x],tcolCase[y]]

(* --------------- Coefficient Rules ------------------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 SVExpandRule =  wrapper[c_~SVTimes~v_] :> ExpandAll[c]~SVTimes~v;
 SVFactorRule =  wrapper[c_~SVTimes~v_] :> Factor[c]~SVTimes~v;
 SVSimplifyRule = wrapper[c_~SVTimes~v_] :> Simplify[c]~SVTimes~v
]
 
(* --------------- Sort vector sum --------------------- *)

VOrder[SVTimes[_.,x_],SVTimes[_.,y_]] := Order[x,y]
VOrderQ[SVTimes[_.,x_],SVTimes[_.,y_]] := OrderedQ[{x,y}]
VSameQ[SVTimes[_.,x_],SVTimes[_.,y_]] := SameQ[x,y]

VSort[sm_VPlus] := Sort[sm, VOrder[#1,#2]>=1&]
VSort[sm_] := sm

(* ============  DOMAIN : Common ============= *)

NewDomain[Common]

Common[GPlus, GTimes, GPower]

GPlus[x___, 0, y___] := GPlus[x,y]
GPlus[] = 0;
GTimes[___, 0, ___] = 0

Attributes[GTimes] = {Listable, OneIdentity}
Attributes[GPlus] =  {Listable, OneIdentity}

(*UnitElement[Common] ^= 1;*)
Default[GTimes] := 1
Default[GPlus] := 0

STimesOp[Common] ^= GTimes
PlusOp[Common] ^= GPlus
(* SumOp[GPlus->GSum] *)
PowerOp[GTimes->GPower]

(* =========================================================== *)

(* ----------- PROPERTY : Additive -------------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 AdditiveRule[f_, First] :=
 With[{ plx=PlusOp[Domain[f,First]], plf=PlusOp[Domain[f]] },
   With[{ smx=SumOp[plx], smf=SumOp[plf] },
     { wrapper[f[plx[y___], z___]] :> (f[#,z]& /@ Unevaluated[plf[y]]),
       If [smx===None || smf===None, Unevaluated[],
          wrapper[f[smx[y_,iter__], z___]] :> smf[Evaluate[f[y,z]], iter] ]
     }
 ] ];
 AdditiveRule[f_, Last] :=
 With[{ plx=PlusOp[Domain[f,Last]], plf=PlusOp[Domain[f]] },
   With[{ smx=SumOp[plx], smf=SumOp[plf] },
     { wrapper[f[x___, plx[y___]]] :> (f[x,#]& /@ Unevaluated[plf[y]]),
       If [smx===None || smf===None, Unevaluated[],
          wrapper[f[x___, smx[y_,iter__]]] :> smf[Evaluate[f[x,y]], iter] ]
     }
 ] ];
 AdditiveRule[f_] :=
 With[{ plx=PlusOp[Domain[f,All]], plf=PlusOp[Domain[f]] },
   With[{ smx=SumOp[plx], smf=SumOp[plf] },
     { wrapper[f[x___, plx[y___], z___]] :> (f[x,#,z]& /@ Unevaluated[plf[y]]),
       If [smx===None || smf===None, Unevaluated[],
          wrapper[f[x___, smx[y_,iter__], z___]] :>
					smf[Evaluate[f[x,y,z]], iter] ]
     }
 ] ]
]

NewProperty[ Additive, {Rule} ]

(* ----------- PROPERTY : Linear -------------- *)

LinearRule[args__] := 
  Flatten[{ ZeroArgRule[args], AdditiveRule[args], HomogenRule[args,1] }]

(* NewProperty[Linear, {Flag, Also->{ZeroArg,Additive,Homogen}}] *)
NewProperty[Linear, {Rule}]

(* ----- Rule : Extract the factors from scalar*domain ------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 ScalarFactorRule[domain_] := Flatten @
  With[{plus=PlusOp[domain], svtimes=STimesOp[domain]},
   { wrapper[ x_plus /; MatchQ[x, wrapper[plus[__svtimes]]] ] :> 
       With[{d=PolynomialGCD @@ First /@ x }, 
             svtimes[d, MapAt[ Cancel[#1/d]&, #, 1]& /@ x]],
     With [{sum=SumOp[plus]},
      If [sum=!=None, 
	{ wrapper[ sum[svtimes[s_,x_], iter__] ] :> svtimes[Sum[s,iter],x] /;
		FreeQ[x, First /@ Alternatives[iter]],
	  wrapper[ sum[svtimes[s_,x_], iter__] ] :>
           With[{d=Factor[s], ptrn = First /@ Alternatives[iter]},
	      With[{d = If[Head[d]===Times, Select[d, FreeQ[#,ptrn]&],
			  (*else*) If [ FreeQ[d,ptrn], d, 1 ] ] },  
		svtimes[d, sum [ Evaluate[svtimes[Cancel[s/d], x]], iter] ] ]]
	},
      (*else*) {}
    ]]
   }]
]

(* ------------ Rule : LinearCollectRule --------------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 LinearCollectRule[f_] :=
  With[{dmex=Domain[f], dmin=Domain[f,All]},
    With[{plex=PlusOp[dmex], plin=PlusOp[dmin],
	  svex=STimesOp[dmex], svin=STimesOp[dmin]},
      { wrapper[ plex[ svex[c1_.,f[a___,x_,b___]], z___, svex[c2_.,f[a___,y_,b___]]] ]
			 :> plex[f[a,plin[svin[c1,x],svin[c2,y]],b], z],
	wrapper[f[x___, svin[c_,v_], y___]] :> svex[c, f[x,v,y]],
	Sequence @@ ScalarFactorRule[dmin],
        With[{smex=SumOp[plex], smin=SumOp[plin]},
	 If [ smex=!=None && smin=!=None,
	   wrapper[ smex[svex[c_.,f[a___,x_,b___]], iter__]] :> 
			f[a,smin[Evaluate[svin[c,x]],iter],b] /;
			    FreeQ[{a,b}, First /@ Alternatives[iter]],
	   (*else*) Unevaluated[]
       ] ]
      }
   ] ];
 LinearCollectRule[f_,First] :=
  With[{dmex=Domain[f], dmin=Domain[f,First]},
    With[{plex=PlusOp[dmex], plin=PlusOp[dmin],
	  svex=STimesOp[dmex], svin=STimesOp[dmin]},
      {wrapper[ plex[ f[x_,b___], z___, f[y_,b___] ] ] :> plex[f[plin[x,y],b], z],
       wrapper[ svex[ c_, f[x_,b___] ] ] :> f[svin[c,x],b],
       With[{smex=SumOp[plex], smin=SumOp[plin]},
	 If [ smex=!=None && smin=!=None,
	   wrapper[ smex[f[x_,b___], iter__]] :> f[smin[x,iter],b] /;
		FreeQ[b, First /@ Alternatives[iter]],
	   (*else*) Unevaluated[]
       ] ]
      }
   ] ];
 LinearCollectRule[f_,Last] :=
  With[{dmex=Domain[f], dmin=Domain[f,Last]},
    With[{plex=PlusOp[dmex], plin=PlusOp[dmin],
	  svex=STimesOp[dmex], svin=STimesOp[dmin]},
      {wrapper[ plex[ f[a___,x_], z___, f[a___,y_] ] ] :> plex[f[a,plin[x,y]], z],
       wrapper[ svex[ c_, f[a___,x_] ] ] :> f[a,svin[c,x]],
       With[{smex=SumOp[plex], smin=SumOp[plin]},
	 If [ smex=!=None && smin=!=None,
	   wrapper[ smex[f[a___,x_], iter__]] :> f[a,smin[x,iter]] /;
		FreeQ[a, First /@ Alternatives[iter]],
	   (*else*) Unevaluated[]
       ] ]
      }
   ] ]
]

(********************  MatchList ************************)
(*  Builds list of terms in "expr" matching "patrn"	*)

MatchList[expr_, patrn_, func_:(#&)] :=
( MatchPatrn = patrn;
  MatchFunc = func;
  Union[MatchScan[expr]]
)

MatchScan = 
 Which [ MatchQ[#, MatchPatrn],  {MatchFunc[#]},
	  AtomQ[#], {},
	  True, Flatten[MatchScan /@ ReplacePart[#,List,0], 1]
  ]&

(********************  WithUnique ************************)

WithUnique[{smb__}, body_] := body /.
   ( (# -> Unique[StringTake[ToString[#],1]<>"$i",{Temporary}])& /@ {smb} )
Attributes[WithUnique] = {HoldRest};

(******************** UniqueCounters ************************)

UniqueCounters[expr_] :=
( ui$list = {};
  ui$res = UniqueCountersScan[expr];
  ui$list = Flatten[ui$list];
  UniqueCounters[ui$list, ui$res]
)

UniqueCountersScan[(hd:VSum|Sum|Table)[exi_,iter__]] :=
 (ui$tmp = UniqueCountersScan[exi];
  ui$ind = First /@ {iter}; 
  ui$uniq = Unique[StringTake[ToString[#],1]<>"$i",{Temporary}]& /@ ui$ind;
  ui$list = {ui$list, ui$uniq};
  hd[Evaluate[ui$tmp],iter] /. Thread[ui$ind->ui$uniq]
 )

UniqueCountersScan[ex_/;AtomQ[ex]] := ex
UniqueCountersScan[ex_] := Evaluate /@ UniqueCountersScan /@ ex

 (* ============ Functions, Operations, Parameters =========== *)

(***************** Parity ********************)

SetProperties[P, { Scalar, Vector->_, TestFirst, Homogen->0,
	ThreadGraded->Plus2, LogPower->Times2 }]

Plus2[x___] := PolynomialMod[Plus[x],2]
Times2[x___] := PolynomialMod[Times[x],2]

(* ------ Rule for simplify (-1)^parity ------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  SimplifySignRule := ( wrapper[(-1)^x_] :> (-1)^SimplifySignExp[x] )]

SimplifySignExp[expr_] :=
  ( PolynomialMod [ Expand [expr //. Mod[x_,2]:>x], 2 ] ) 

SimplifySign[expr_] := expr /. SimplifySignRule /.
  P[e_]^_:>P[e] /. (-1)^(1+n_) :> - (-1)^n

(* ------- Checking the parity ------- *)

SetProperties[Parity, { Scalar, Vector->_, Homogen->0,
	ThreadGraded->Plus2, LogPower->Times2 }]

Scalar[Mixed]
Mixed/: Plus[___,Mixed,___] = Mixed
Mixed/: Times[Mixed,c_/;c=!=0] = Mixed
Mixed/: Power[Mixed,_] = Mixed
Mixed/: Mod[Mixed,_] = Mixed

Parity[v_] := P[v]

Parity[v_VPlus] :=
 With[{pp = Union[SimplifySign /@ Parity /@ List @@ v]},
   If[Length[pp]==1, First[pp], Mixed]]

Parity[v_VSum] :=
 With[{pp = SimplifySign[Parity[First[v]]],
	 ind = First /@ Rest[List @@ v]},
   If[Select[ ind, (!FreeQ[pp,#])&, 1], Mixed, pp]]


(***************** Delta function ********************)

Scalar[Delta]

Delta[a_/;a!=0] = 0
Delta[0] = 1
Delta[-a_] := Delta[a]
Delta/: a_*Delta[a_] = 0

Delta[a_,a_] = 1
(Delta[a_,b_]/; a != b) := 0 

(***************** Tensor product **********************)

Unprotect[CircleTimes]
SetProperties[CircleTimes, {Vector, Vector->__, Linear, (*IdArg,*)
   Graded, DegTimes, PowerOp->tPower } ]
Attributes[CircleTimes] = { Flat, OneIdentity }

Format[x_CircleTimes /; Length[x] == 1, OutputForm] := x[[1]]
Format[x_CircleTimes /; Length[x] == 1, StandardForm] := x[[1]]
Format[x_CircleTimes /; Length[x] == 1, TraditionalForm] := x[[1]]


(* ------ Symmetric product - see VTimes -------- *)

(* ----------- Degree in VTimes ----------------- *)

SetProperties[Deg, {Scalar, Vector->First}];
Deg[(f_?DegTimesQ)[v___], x___] := Deg[#,x]& /@ Unevaluated[Plus[v]]
Deg[(f_?DegPowerQ)[v_,n_], x___] := n*Deg[v,x]
Deg[expr_, x_]/;MatchQ[expr,x] := 1
Deg[expr_, x_]/;FreeQ[expr,x] := 0
Deg[SVTimes[c_,v_],x___] := Deg[v,x]
Deg[e_VPlus,x___] :=
  With[{dg=Expand[Deg[#,x]]& /@ (List @@ e)}, If[SameQ@@dg, dg[[1]], Mixed]]
Deg[VIf[c_,v_],x___] := Deg[v,x]
Deg[VSum[v_,iter__],x___]:=
  With[{dg=Expand[Deg[v,x]],cnt=First/@Alternatives[iter]},
    If[FreeQ[dg,cnt], dg, Mixed]]

(*
pDeg[expr_VTimes, x_] := Plus @@ Cases[expr, VPower[x,p_.] :> p]
pDeg[VPower[expr_,p_],x_] := p pDeg[expr,x]
pDeg[expr_, x_] := If[expr===x, 1, 0];
*)

(* ----------- Partial derivations ------------ *)

Off[Part::pspec]

SetProperties[{LDer, RDer}, {Vector, Vector->First, Linear->First}];
LDer[VPower[f_, n_], x__] :=
 If[DivPowersQ[f],
   VTimes[VPower[f, n-1], LDer[f, x]],
   SVTimes[n, VTimes[VPower[f, n-1], LDer[f, x]]]]
LDer[f_VTimes, x_, b_] := Module[{n=Length[f],sf=1,res={}},
		Do[ res={res, SVTimes[sf,ReplacePart[f,LDer[f[[i]],x,b],i]]};
      sf=sf*(-1)^(P[f[[i]]]P[x]),{i,1,n}]; VPlus@@Flatten[res]]

LDer[f_,x_,b_]:=VIf[SameElement[f,x], VTimes[]] /; MatchQ[f,b]

P[e_LDer] ^:= Plus2[P[e[[1]]], P[e[[2]]]]

HoldPattern[LDer[LDer[f_,x_,b_],y_,b_]] := 
  SVTimes[(-1)^(P[x]P[y]), LDer[LDer[f,y,b],x,b]] /; !OrderedQ[{y,x}]

\!\(Format[HoldPattern[LDer[f_, x_, b_]],OutputForm] := HoldForm[\[PartialD]\_x\ f]\)

LDer/: MakeBoxes[e:HoldPattern[LDer[f_,x_,b_]],fmt_] :=
  With[{bx=MakeBoxes[x,fmt], bf=PrecedenceBox[f,600,fmt]},
    InterpretationBox[RowBox[{
          SubscriptBox["\[PartialD]", bx], bf}], e]]

RDer[VPower[f_,n_],x__] :=
 If[DivPowersQ[f],
   VTimes[RDer[f,x], VPower[f,n-1]],
   SVTimes[n,VTimes[RDer[f,x], VPower[f,n-1]]]]
RDer[f_VTimes, x_, b_] := Module[{n=Length[f],sf=1,res={}},
		Do[ res={res, SVTimes[sf,ReplacePart[f,RDer[f[[i]],x,b],i]]};
      sf=sf*(-1)^(P[f[[i]]]P[x]),{i,n,1,-1}]; VPlus@@Flatten[res]]

RDer[f_,x_,b_]:=VIf[SameElement[f,x], VTimes[]] /; MatchQ[f,b]

P[e_RDer] ^:= Plus2[P[e[[1]]], P[e[[2]]]]

On[Part::pspec]	


Vector[ZLDer,ZRDer];
ZLDer[x__][expr_]:=LDer[expr,x];
ZRDer[x__][expr_]:=RDer[expr,x];

Unprotect[OrderedQ]
OrderedQ[{___,_ZLDer,__}]=False
OrderedQ[{x___,_ZLDer}]:=OrderedQ[{x}]
Protect[OrderedQ]


MakeBoxes[HoldPattern[ZLDer[x_,b_]],TraditionalForm]^:=
  FractionBox["\[PartialD]", 
      RowBox[{"\[PartialD]", MakeBoxes[x,TraditionalForm]}]]

MakeBoxes[e:HoldPattern[ZLDer[x_,b_]], fmt_] ^:=
  With[{bx=MakeBoxes[x, fmt]},
    InterpretationBox[SubscriptBox["\[PartialD]", bx], e]]

\!\(Format[HoldPattern[ZLDer[x_, b_]], OutputForm] := "\<\[PartialD]\>"\_x\)

(* Comparison of elements of the basis *)

SameElement[f_,f_]:=True
SameElement[f_,g_]:=False/;AtomQ[f]||AtomQ[g]||Head[f]=!=Head[g]
SameElement[f_[a___], f_[b___]] :=
  Module[{n = Length[{a}], i, same = True, el},
    If[n != Length[{b}] , Return[False]];
    For[i = 1, i <= n, i++,
      el = If[Domain[f, i, n]===Vector, SameElement[{a}[[i]], {b}[[i]]], {a}[[i]] == {b}[[i]]];
      If[el === False, Return[False], same = same && el]];
    same];

(*************** Exterior product ******************)

(*
Attributes[Wedge] = { Flat, Listable, OneIdentity };
*)

(*ep[x_] := Unevaluated[x]*)
(*ep[] = Id*)

(*
SetProperties[Wedge, {Vector, Vector->__, Linear, (*IdArg,*) Graded,
		DegTimes, Symmetric } ]
Format[e_Wedge/;Length[e]==1] := e[[1]]
Format[Wedge[]] := "I"
*)

(*
Wedge[___,x_/;P[x]===1,x_,___] = 0;
Wedge[y___,x_^(n1_:1), x_^(n2_:1),z___] := Wedge[y,x^(n1+n2),z];
Wedge[y___, (x_/;P[x]==1)^(n_/;n>1), z___] := 0;
*)

Format[e:Wedge[x_]] := x
Format[Wedge[]] := "I"

MakeBoxes[e:Wedge[x_], fmt_] := InterpretationBox[MakeBoxes[x,fmt],e];
MakeBoxes[Wedge[], fmt_] := InterpretationBox["I", e];

SymmetricRule[Wedge] ^:= {}
SkewSymmetricRule[Wedge] ^:= {}

SetProperties[Wedge, {Vector, Vector->__, Linear, Symmetric, Graded, PowerOp->wPower} ]

Attributes[wedge] = {OneIdentity};
SetProperties[wedge, {Vector, Vector->_, Graded, DegTimes} ]
P[wedge] ^= 0;
PowerOp[wedge] ^= wPower;

SetProperties[wPower, {Vector, Vector->First, Scalar->Last}]


Format[wedge[x___],OutputForm] := HoldForm[Wedge[x]]
Format[wedge[x___],TeXForm] := HoldForm[Wedge[x]]

MakeBoxes[x_wedge, fmt_] ^:= InfixBoxes[x, "\[Wedge]", 440, "I", fmt];

Wedge[x_,y_] := Wedge2[x, y, PowerOp[Wedge]]/.LinearRule[wedge];

Wedge2[x_wedge,y_wedge, None]:=
  Module[{lx=Length[x],ly=Length[y],px,res={},i=1,j=1,k,xi,yj,pyj,sgn=1,skew=SkewSymmetricQ[Wedge]},
	If[lx==0, Return[y]];
	If[ly==0, Return[x]];
	px=P/@x;
	If[skew, px=1-px];
	For[k=lx-1,k>=1,k--, px[[k]]+=px[[k+1]]];
	xi=x[[1]];
	yj=y[[1]];
	pyj=P[yj];
	If[skew, pyj=1-pyj];
	While[True,
	  If[OrderedQ[{xi,yj}],
		If[pyj==1&&xi===yj,Return[0]];
		res={res,xi};
		If[i==lx,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[y,j-1]]]];
		xi=x[[++i]],
	  (*else*)
		res={res,yj};
		sgn *=(-1)^(px[[i]]*pyj);
		If[j==ly,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[x,i-1]]]];
		yj=y[[++j]];
		pyj=P[yj];
                If[skew, pyj=1-pyj]]]]

Wedge2[x_, y_wedge, None]:=
  Module[{ly=Length[y],px=P[x],py=0,pyj,j,yj,skew=SkewSymmetricQ[Wedge]},
	If[ly==0, Return[wedge[x]]];
        If[skew, px = 1-px];
	For[j=1, j<=ly, j++,
		yj=y[[j]];
	  If[OrderedQ[{x,yj}],
	    Return[If[px===1&&x===yj, 0, SVTimes[(-1)^(px*py), Insert[y,x,j]]]],
	  (*else*)
            pyj = P[yj];
            If[skew, pyj=1-pyj];
	    py += pyj]];
	SVTimes[(-1)^(px*py), Append[y,x]]]

Wedge2[x_wedge,y_,None]:=
  Module[{lx=Length[x],px=0,py=P[y],i,xi,pxi,skew=SkewSymmetricQ[Wedge]},
	If[lx==0, Return[wedge[y]]];
        If[skew, py = 1-py];
	For[i=lx,i>=1,i--,
	  xi=x[[i]];
	  If[OrderedQ[{xi,y}],
            Print["x[",i,"]=",xi];
	    Return[If[py===1&&xi===y, 0, SVTimes[(-1)^(px*py),Insert[x,y,i+1]]]],
	  (*else*)
            pxi = P[xi];
            If[skew, pxi=1-pxi];
	    px += pxi]];
    SVTimes[((-1)^(px*py)),Prepend[x,y]]]

Wedge2[x_,y_,None]:=
  With[{px=P[x],pw=If[SkewSymmetricQ[Wedge],1,0]},
    If[OrderedQ[{x,y}],
	  If[px=!=pw && x===y, 0, wedge[x,y]],
	(*else*)
	  SVTimes[(-1)^((px+pw)*(P[y]+pw)), wedge[y,x]]]]

Wedge2[x_wedge, y_wedge, pow_]:=  Wedge3[List@@x, List@@y, pow]

Wedge3[x_, y_, pow_] :=
  Module[{lx=Length[x],ly=Length[y],px,res={},i=1,j=1,k,xi,yj,pyj,sgn=1,skew=SkewSymmetricQ[Wedge],bi,bj,di,dj,r,s},
	If[lx==0, Return[y]];
	If[ly==0, Return[x]];
	px=P/@x;
	If[skew, px=1-px];
	For[k=lx-1,k>=1,k--, px[[k]]+=px[[k+1]]];
	xi=x[[1]];
	yj=y[[1]];
	pyj=P[yj];
	If[skew, pyj=1-pyj];
	While[True,
	  bi = If[Head[xi]===pow, xi[[1]], xi];
          bj = If[Head[yj]===pow, yj[[1]], yj];
          Which[
            bi===bj,
		If[pyj==1 && yj===bj,Return[0]];
		{s,r} = wPow2[xi,yj,pow];
		res={res,r};
		sgn *=s;
		If[i==lx,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[y,j]]]];
		xi=x[[++i]];
		sgn *= (-1)^(px[[i]]*pyj);
		If[j==ly,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[x,i-1]]]];
		yj=y[[++j]];
		pyj=P[yj];
                If[skew, pyj=1-pyj],
	    OrderedQ[{bi,bj}],
		res={res,xi};
		If[i==lx,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[y,j-1]]]];
		xi=x[[++i]],
	    True, (*else*)
		res={res,yj};
		sgn *=(-1)^(px[[i]]*pyj);
		If[j==ly,
		  Return[sgn~SVTimes~wedge[Sequence@@Flatten[res],Sequence@@Drop[x,i-1]]]];
		yj=y[[++j]];
		pyj=P[yj];
                If[skew, pyj=1-pyj]]]]


wPow2[pow_[x_,n1_],pow_[x_,n2_],pow_] :=
 {If[DivPowersQ[x,pow], Binomial[n1+n2,n1], 1], pow[x, n1+n2]}

wPow2[x_,pow_[x_,n2_],pow_] :=
 {If[DivPowersQ[x,pow], Binomial[1+n2,1], 1], pow[x, 1+n2]}

wPow2[pow_[x_,n1_],x_,pow_] :=
 {If[DivPowersQ[x,pow], Binomial[n1+1,1], 1], pow[x, n1+1]}

wPow2[x_,x_,pow_] :=
 {If[DivPowersQ[x,pow], 2, 1], pow[x, 2]}
 

Wedge2[x_, y_wedge, pow_]:=  Wedge3[{x}, List@@y, pow]
Wedge2[x_wedge, y_, pow_]:=  Wedge3[List@@x, {y}, pow]
Wedge2[x_, y_, pow_]:=  Wedge3[{x}, {y}, pow]

Wedge[x_,y_,z__]:= Wedge[Wedge[x,y],z];

Wedge[x_] := x
Wedge[] := wedge[]
Wedge[x_,wedge[]] ^:= x
Wedge[wedge[],x_] ^:= x

wedge[x_] := Unevaluated[x]

(*
Jacobi[brk_->Wedge] := Jacobi[brk->wedge]
UnJacobi[brk_->Wedge] := UnJacobi[brk->wedge]
JacobiRule[brk_,Wedge] ^:= JacobiRule[brk,wedge]

Leibniz[fn_->Wedge] := Leibniz[fn->wedge]
UnLeibniz[fn_->Wedge] := UnLeibniz[fn->wedge]
LeibnizRule[fn_,Wedge] ^:= LeibnizRule[fn,wedge]
*)

LeibnizExpandFn[wedge] ^= LeibnizExpandWedge

LeibnizExpandWedge[ f_[prm___,expr_], par_ ] := 
  Module [{ m, fm, s=1, s1, ph=P[Head[expr]] },
    If[!NumberQ[ph],
      Message[Leibniz::par, Head[expr]];
      ph = 0];
    VPlus @@ Table[
      m = expr[[i]];
      s1 = s;
      s *= (-1)^(par~Times~(P[m]+ph));
      If [(fm = f[prm,m])===0, 0,
	 (*else*) s1 ~SVTimes~ Wedge[Take[expr,i-1],fm, Drop[expr,i]]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]

LeibnizExpandWedge[ f_[prm___,expr_], 0 ] := 
  Module [{ m, fm },
    VPlus @@ Table[
      m = expr[[i]];
      If [(fm = f[prm,m])===0, 0,
	 (*else*) Wedge[Take[expr,i-1],fm, Drop[expr,i]]
      ],
     (*sum index*) { i, Length[expr]} 
    ]
 ]
 
wedge /: LeibnizExpandPower[f_[prm___,wPower[v_,n_]], wedge] :=
 If[DivPowersQ[v,wPower],
    f[prm,v] ~Wedge~ wPower[v,n-1],
    n ~SVTimes~ (f[prm,v] ~Wedge~ wPower[v,n-1])]


Symmetric[Wedge] ^:= True /; symPower[PowerOp[Wedge],1]
SkewSymmetric[Wedge] ^:= True /; symPower[PowerOp[Wedge],0]
AntiSymmetric[Wedge] ^:= True /; symPower[PowerOp[Wedge],0]
AntiSkewSymmetric[Wedge] ^:= True /; symPower[PowerOp[Wedge],1]

UnSymmetric[Wedge] ^:= True /; unSymPower[PowerOp[Wedge],1]
UnSkewSymmetric[Wedge] ^:= True /; unSymPower[PowerOp[Wedge],0]
UnAntiSymmetric[Wedge] ^:= True /; unSymPower[PowerOp[Wedge],0]
UnAntiSkewSymmetric[Wedge] ^:= True /; unSymPower[PowerOp[Wedge],1]

symPower[__] = False
unSymPower[__] = False
With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  symPower[pw_Symbol, asym_] := (wrapper[ (x_/;P[x]==asym)~pw~(n_/;n!=1&&n!=-1)] := 0; False);
  unSymPower[pw_Symbol, asym_] := (wrapper[ (x_/;P[x]==asym)~pw~(n_/;n!=1&&n!=-1)] =.; False)
]

(********* Coefficient Times ************)

CTimes[op_, props___] :=
  ((*Attributes[op] = {OneIdentity};*)
   SetProperties[op,
       {Vector, Vector->__, Graded, ZeroArg, DegTimes, props}];
   Default[op, 1, 2] = VTimes[];
   op[c_?ScalarQ,v_] := SVTimes[c, op[VTimes[],v]];
  )


(********* Tensor product of expressions ************)

(* Normal form :   v >< w1 + v >< w2   and   (v1+v2) >< w   *)

Attributes[NonCommutativeMultiply] = {OneIdentity};
SetProperties[NonCommutativeMultiply,
       {Vector, Vector->__, Graded, ZeroArg, (* IdArg, Linear*) DegTimes,
		Output->InfixFormat["><", Prec->150, Empty->"I"],
		TeX->InfixFormat["\\otimes ", Prec->150, Empty->"I"] } ]


(*Default[NonCommutativeMultiply] := Id*)

(* -------------------- Id --------------------------- *)
(*
Vector[Id]
P[Id] ^= 0
Act[_,Id] ^= 0
*)

Vector[ZId];
ZId[x_]:=x

(* --------- PROPERTIES : Dim, PDim, PList ----------- *)

UpUnset[tag_, ptrn_] :=
 ( UpValues[tag] =
	Select[UpValues[tag], !MatchQ[ Hold @@ #[[1]], Hold[ptrn]]& ]
 )
Attributes[UpUnset] = {HoldRest}


PiOrder = False;

Dim[obj_->val_Alternatives] :=
( UpUnset[obj, _Dim|_PDim|_P|_PList];
  Dim[obj] ^= Plus @@ val;
  PDim[obj] ^= List @@ If [PiOrder, Reverse[val], val];
  If [val[[1]]===0, P[_obj] ^= If[PiOrder, 0, 1],
  (*else*) If [val[[2]]===0, P[_obj] ^= If[PiOrder, 1, 0] ]];
) /; Length[val]==2


Dim[obj_->val_] :=
( UpUnset[obj, _Dim|_PDim|_P|_PList];
  Dim[obj] ^= val;
  PDim[obj] ^= If [PiOrder, {0, val}, {val, 0}];
  P[obj[i_ /; i>0 && i<=val]] ^= If[PiOrder, 1, 0];
) /; Head[val]=!=List


Dim[obj_->{0, val___}] :=
  Block[{PiOrder = ! PiOrder}, Dim[obj->{val}]];

(*
Dim[obj_->{dm__Integer, Infinity}] :=
( Dim[obj->{dm}];
  With [ { tail=If[EvenQ[Length[{dm}]]==PiOrder, 0, 1], hdim=Dim[obj] },
   Dim[obj] ^= Infinity;
   PDim[obj] ^= ReplacePart[ PDim[obj], Infinity, tail+1 ];
   P[obj[i_/;i>hdim]] ^= tail
  ];
)
*)

Dim[obj_->val:{__Integer}] :=
  PList[obj->Flatten[MapIndexed[ Table[If[EvenQ[#2[[1]]],1,0], {#1}]&, val]] ];

Dim[obj_->{dm__Integer, j_}] :=
( Dim[obj->{dm}];
  With [ {hdim=Dim[obj] },
   Dim[obj] ^= Plus[hdim,j];
   If[EvenQ[Length[{dm}]]==PiOrder,
     PDim[obj] ^= {PDim[obj][[1]], j+PDim[obj][[2]]};
     P[obj[i_/;i>hdim]] ^= 1,
  (* else *)
     PDim[obj] ^= {j+PDim[obj][[1]], PDim[obj][[2]]};
     P[obj[i_/;i>hdim]] ^= 0]
  ];
)

Dim[obj_->{Infinity, dm__Integer}] :=
(  Dim[obj->{0, dm}];
   Dim[obj] ^= Infinity;
   PDim[obj] ^= ReplacePart[ PDim[obj], Infinity, If[PiOrder, 2, 1]];
   P[obj[i_/;i<=0]] ^= If[PiOrder, 1, 0];
)

Dim[obj_->{Infinity, dm__Integer, Infinity}] :=
( Dim[obj->{0, dm}];
  With [ { tail=If[EvenQ[Length[{dm}]], 1, 0], hdim=Dim[obj] },
   Dim[obj] ^= Infinity;
   PDim[obj] ^= If [tail===1, { Infinity, Infinity },
			ReplacePart[ PDim[obj], Infinity, If[PiOrder, 2, 1]]
		];
   P[obj[i_ /;i>hdim]] ^= If[PiOrder, 1-tail, tail];
   P[obj[i_ /; i<0 ]] ^= If[PiOrder, 1, 0];
  ];
)

Dim[obj_->{j_}] := Dim[obj->j]

(*
Dim[obj_->{i_Integer, j_ /;!IntegerQ[j]}] :=
( UpUnset[obj, _Dim|_PDim|_P|_PList];
  Dim[obj] ^= Plus[i,j];
  If[PiOrder,
    PDim[obj] ^= {j,i};
    P[obj[k_ /; IntegerQ[k] && k>0]] ^:= Evaluate[If[k<=i, 1, 0]],
  (* else *)
    PDim[obj] ^= {i,j};
    P[obj[k_ /; IntegerQ[k] && k>0]] ^:= Evaluate[If[k<=i, 0, 1]]]
) 

Dim[obj_->{i1_Integer, i2_Integer, j_ /;!IntegerQ[j]}] :=
( UpUnset[obj, _Dim|_PDim|_P|_PList];
  Dim[obj] ^= Plus[i1,i2,j];
  If[PiOrder,
	PDim[obj] ^= {i2,Plus[i1,j]};
    P[obj[k_ /; IntegerQ[k] && k>0]] ^:=
      Evaluate[If[Evaluate[Plus[i1,1]<=k<=Plus[i1,i2]], 0, 1]],
  (* else *)
    PDim[obj] ^= {Plus[i1,j],i2};
    P[obj[k_ /; IntegerQ[k] && k>0]] ^:=
      Evaluate[If[Evaluate[Plus[i1,1]<=k<=Plus[i1,i2]], 1, 0]]]
) 
*)

PList[obj_->val_] :=
( UpUnset[obj, _Dim|_PDim|_P|_PList];
  PList[obj] ^= If[PiOrder, 1-val, val];
  Dim[obj] ^= Length[val];
  PDim[obj] ^= Count[PList[obj], #]& /@ {0,1};
  P[obj[ i_/; Evaluate[i>0 && i<=Dim[obj]] ]] ^:= PList[obj][[i]];
) 

FDim[v_] := 
 With[{dim=PDim[v]},
   If[dim[[2]]===0, dim[[1]],
    (*else*) StringForm["``|``",dim[[1]], dim[[2]] ]
   ]
 ]




(*************** Algebra operation *************]
 *  "Act" is the operation in Lie (Super)Algebra and
 *     the action on the modules.
 *  "act" is the unevaluated form of "Act" (output format - [x,y])
 *  Squaring[x,Act] replaces Act[x,x] for odd x and fields
 *     of characteristic 2
[***********************************************)

Bracket::undef = "Action of \"``\" on \"``\" not defined."
Options[NewBracket] ^= {Parity->0, Grade->0,
        Symbol->Auto, Output->ArgForm["[`1`,`2`]"],
	Standard->SeqForm["[",#1,",\[ThinSpace]",#2,"]"],
	Traditional->SeqForm["[",#1,",\[ThinSpace]",#2,"]"],
	TeX->SeqForm["[",#1,",\[ThinSpace]",#2,"]"]
 }

(*ArgForm[form_] := StringForm[form, Sequence@@#]&  *)
(*SeqForm[form__] := (SequenceForm[form]& @@ #)&  *)
ArgForm[form_] := Function[ex, StringForm[form, Sequence@@Unevaluated[ex]], {HoldAll}]
SeqForm[form__] := Function[ex,(SequenceForm[form]& @@ Unevaluated[ex]), {HoldAll}]

NewBracket[Brk_,opts___] :=
Module[{brk, str, cap, p, gr},
  brk = Symbol /. {opts} /. Options[NewBracket];
  p=Parity /.{opts} /. Options[NewBracket];
  gr = Grade /.{opts} /. Options[NewBracket];
  If [brk===Auto,
    str = ToString[Brk]; 
    cap = StringTake[str,1];
    str = StringDrop[str,1];
    Bracket$[ToExpression[ToUpperCase[cap]<>str], 
	     ToExpression[ToLowerCase[cap]<>str], p, gr, opts],
  (*else*)
    Bracket$[Brk,brk,p,gr,opts]
  ]
]

Bracket$[Brk_, brk_, p_, gr_, opts___] :=
Module[{out, tex, std, trad},
  {out,tex,std,trad} = {Output, TeX, Standard, Traditional} /.
			 {opts} /. Options[NewBracket];
  SetProperties[{Brk, brk},
		{ Vector, Vector->__, Linear, Graded, Output->out, TeX->tex,
		        Grade->gr, Parity->p, DegTimes,
			Standard->std, Traditional->trad }];
  OpSymbol[Brk] ^= brk;
  Operator[brk] ^= Brk;
  P[Brk] ^= p;
  P[brk] ^= p;
  brk[x_,x_] := 0 /; P[x]==p;
  If[p==0,
   brk/: Brk[z_, brk[v_,w_]] :=
     VPlus [ brk[Brk[z,v],w], ((-1)^(P[z]*P[v])) ~SVTimes~ brk[v,Brk[z,w]] ] /.
				brk[x__/;FreeQ[{x},brk]] :> Brk[x];
   brk/: Brk[brk[v_,w_],z_] :=
     VPlus [ brk[v,Brk[w,z]], ((-1)^(P[z]*P[w])) ~SVTimes~ brk[Brk[v,z],w] ] /. 
				brk[x__/;FreeQ[{x},brk]] :> Brk[x];
   Brk[x_, Squaring[y_, brk]] := Brk[Brk[x, y], y];
   Brk[Squaring[y_, brk], x_] := Brk[y, Brk[y, x]],
  (*else*)
   brk/: Brk[z_, brk[v_,w_]] :=
     VPlus [ brk[Brk[z,v],w], ((-1)^((P[z]+p)*(P[v]+p))) ~SVTimes~ brk[v,Brk[z,w]] ] /.
				brk[x__/;FreeQ[{x},brk]] :> Brk[x];
   brk/: Brk[brk[v_,w_],z_] :=
     VPlus [ brk[v,Brk[w,z]], ((-1)^((P[z]+p)*(P[w]+p))) ~SVTimes~ brk[Brk[v,z],w] ] /. 
				brk[x__/;FreeQ[{x},brk]] :> Brk[x]
  ];
  Brk[_,_?ScalarQ] = 0;
(*  Brk[n_[i_]/;ValueQ[Image[n]], x_] := Brk[Image[n][[i]], x]; *)
(* Brk[g_, m_/; Head[m]=!=Slot]:=(Message[Bracket::undef, g, m]; brk[g,m]);*)
]

(*Act[g_, m_None] := (Message[Bracket::undef, Head[g], None]; act[g,m])*)


SetProperties[Squaring, {Vector, Vector->First, Homogen->{First,2}, ZeroArg->First}]

Squaring[x_,brk_] := 0 /; P[x]==P[brk]
P[x_Squaring] ^= 0
Grade[Squaring[x_,_]] ^:= 2*Grade[x];
Weight[Squaring[x_,_]] ^:= 2*Weight[x];


Squaring[x_VPlus,brk_] :=
  VPlus[Squaring[#,brk]& /@ x, VSum[brk[x[[i]],x[[j]]], {j,Length[x]},{i,1,j-1}]]

    
Squaring[VIf[x_,cond_], brk_] := VIf[Squaring[x,brk], cond]

Squaring[e:VSum[x_,iter__],brk_] :=
  VPlus[VSum[Squaring[x,brk],iter], SubdiagonalOuter[UniqueCounters[e][[2]], e, brk]]

MakeBoxes[Squaring[x_, _], form_] ^:= SuperscriptBox[$`PrecedenceBox[x, 590, form], "[2]"]
  
SubdiagonalOuter[VSum[x_,xiter_], VSum[y_,yiter_], brk_, iter___] :=
  With[{siter=SubdiagonalIter[xiter, yiter]},
    VSum[brk[x,y], iter, siter]]

SubdiagonalOuter[VSum[x_,xiter_, xmore__], VSum[y_,yiter_,ymore__], brk_, iter___] :=
  VPlus[
    With[{siter=SubdiagonalIter[xiter, yiter]},
      VSum[brk[x,y], iter, siter, xmore, ymore]],
    With[{xx=x/.xiter[[1]]->yiter[[1]]},
      SubdiagonalOuter[VSum[xx,xmore], VSum[y,ymore], brk, yiter, iter]]]


SubdiagonalIter[{i_,from_,to_},{j_,__}] := Sequence @@ {{j,from+1,to},{i,from,j-1}}
SubdiagonalIter[{i_,to_},{j_,__}] := Sequence @@ {{j,2,to},{i,j-1}}
SubdiagonalIter[{i_,from_->to_},{j_,__}] := Sequence @@ {{j,from->to},{i,from->j}}



(********************* Grading,  Weights *********************)

SetProperties[ {Grade, Weight, PolyGrade},
		{Scalar, Vector->First, Homogen->0, ThreadGraded, LogPower->Times, TestFirst}]

WeightMark[dim_Integer, mark___Integer] :=
  Fold[ AddMark, Table[0, {dim}], {mark} ]                       	

(WeightMark[dim_, mrk1___] + WeightMark[dim_, mrk2___]) ^:=
		WeightMark[dim, mrk1, mrk2]
WeightMark[dim_, mr1___, mp_, mr2___, mm_, mr3___] :=
	WeightMark[dim, mr1,mr2,mr3] /; mp+mm==0

AddMark[lst_, i_] := MapAt[#+1&, lst, i] /; i>0
AddMark[lst_, i_] := MapAt[#-1&, lst, -i] /; i<0
AddMark[lst_, 0] := lst

 (* ---------- Define the bracket using the table ----------------- *)
 (* 981101: case of odd bracket *)


TableBracket[g_, Brk_, tbl_, brk_, rng_:Infinity, sqr_:Null] :=
 If[OddQ[P[Brk]],
   If [rng===Infinity || rng===Null,
    Brk[ g[j_], g[i_] ] ^:=
	  If [j<=i, tbl[[i,j]],
	  (*else*)  (-(-1)^((P[g[i]]+1)*(P[g[j]]+1))) ~SVTimes~ tbl[[j,i]]
	  ];
    If[ sqr=!=Null, Squaring[g[i_],Brk] ^:= sqr[[i]]],
   (*else*)
    Brk[ g[j_], g[i_] ] ^:=
      If [ Grade[g[i]]+Grade[g[j]]<=rng,
        If [j<=i,  tbl[[i,j]], 
	     (*else*) (-(-1)^((P[g[i]]+1)*(P[g[j]]+1))) ~SVTimes~ tbl[[j,i]] ]
	   ],
      (*else*)
	   If [j<=i, brk[g[j],g[i]], 
	   (*else*)  (-(-1)^((P[g[i]]+1)*(P[g[j]]+1))) ~SVTimes~ brk[g[i],g[j]] 
	 ];
     If[ sqr=!=Null,
       Squaring[g[i_],Brk] ^:=
         If [ Grade[g[i]]<=rng, sqr[[i]], Squaring[g[i],brk]]]
  ],
 (* else if even *)
  If [rng===Infinity || rng===Null,
    Brk[ g[j_], g[i_] ] ^:=
	  If [j<=i, tbl[[i,j]],
	  (*else*)  (-(-1)^(P[g[i]]*P[g[j]])) ~SVTimes~ tbl[[j,i]]
	  ];
    If[ sqr=!=Null, Squaring[g[i_],Brk] ^:= sqr[[i]]],
   (*else*)
    Brk[ g[j_], g[i_] ] ^:=
      If [ Grade[g[i]]+Grade[g[j]]<=rng,
        If [j<=i,
           tbl[[i,j]],
        (*else*)
           (-(-1)^(P[g[i]]*P[g[j]])) ~SVTimes~ tbl[[j,i]]
	],
      (*else*)
        If [j<=i,
           brk[g[j],g[i]],
        (*else*)
          (-(-1)^(P[g[i]]*P[g[j]])) ~SVTimes~ brk[g[i],g[j]]
	]
      ];
    If[ sqr=!=Null,
       Squaring[g[i_],Brk] ^:=
         If [ Grade[g[i]]<=rng, sqr[[i]], Squaring[g[i],brk]]]
  ]
 ]


VSumNormRule = VSum[v_, iter___] :> VSum[Evaluate[VNormal[v]], iter]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 VSumOutRule[op_] :=
  wrapper[op[x___, VSum[y_,iter__], z___]] :> VSum[Evaluate[op[x,y,z]], iter]
]

VSumOutRule[op_, more__] := VSumOutRule /@ {op, more}

(* -------------- Join VSums --------------- *)

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 JoinVSumRule =
 wrapper[ VPlus[ ex1:(c1_.~SVTimes~VSum[x1_,it1___]), y___,
			ex2:(c2_.~SVTimes~VSum[x2_,it2___])]] :>
     With[{convert=AlignIndex[{it1},{it2}, ex1,ex2]},
	  DPrint[4, convert];
	  y ~VPlus~ VSum[ Evaluate[(SVTimes[c1,x1]/.convert[[1]]) ~VPlus~
		(SVTimes[c2,x2]/.convert[[2]])],
		 Evaluate[ Unevaluated[it1]/.convert[[1]]] ]
	  /; convert=!=False
     ]
]

AlignIndex[it1_, it2_, ex1_, ex2_] :=
  Module[{nind, conv1={}, conv2={}, itm1, itm2, def, ind, ret=True },
    nind = Length[it1];
    If [nind!=Length[it2], Return[False] ];
    ret = Do [ itm1 = it1[[i]]/.conv1;
	 itm2 = it2[[i]]/.conv2;
	 def = Expand[itm2[[2]] - itm1[[2]]];
	 If [ Expand[itm1[[3]]-itm2[[3]]-def]=!=0, Return[False] ];
	 If [itm1[[1]]=!=itm2[[1]],		(* must change index *)
	    If [FreeQ[ex2, itm1[[1]]],
			AppendTo[conv2, itm2[[1]]->itm1[[1]]+def],
	    (*else*) If [FreeQ[ex1, itm2[[1]]],
			AppendTo[conv1, itm1[[1]]->itm2[[1]]-def],
	    (*else*) ind = Unique[ itm1[[1]] ];
		     AppendTo[conv1, itm1[[1]]->ind];
		     AppendTo[conv2, itm2[[1]]->ind+def]
	    ]],
	(*else*) If [def=!=0, conv2 = {conv2, itm2[[1]]->itm1[[1]]+def}]
	],
      {i, nind}
    ];
    If [ret===False, Return[False]];
    {conv1, conv2}
 ]


SplitPtrn[ptrn_][(c_:1)~SVTimes~x_] := {x, c} /;MatchQ[x, ptrn]
SplitPtrn[ptrn_][x_] := {x,$Failed} /; (Message[Split::nomatch,x,ptrn]; True) 


(* ---------  Debug tools -------------- *)

$DPrint = 0
$DPrintLabel=None

DPrint[level_,args___] :=
 If [$DPrint>=level,
   If[$DPrintLabel===None,
     Print[args],
     Print[$DPrintLabel[], " --> ", args]]]

Arrtibutes[DPrint] = {HoldRest}

If [$VersionNumber < 6,
  DateString[] :=
   Module[{y, m, d, h, mn, s},
     {y, m, d, h, mn, s} = Date[];
     ToString[StringForm["``-``-``, ``:``:``",
           y, str$2[m], str$2[d], h, str$2[mn], str$2[s]]]]]

TimeString[] := 
 Module[{y, m, d, h, mn, s},
   {y, m, d, h, mn, s} = Date[];
   ToString[StringForm["``:``:``", h, str$2[mn], str$2[s]]]]

str$2[num_] := With[{s = ToString[num]}, If[num < 10, StringJoin["0", s], s]];

Protect /@ tmp$

(* Field characteristic *)

normalZeroChar =$SNormal;
solveZeroChar = $Solve;


FieldChar[p_] :=
  If[p==0,
    If[$p>0,
      $SNormal = normalZeroChar;
      $Solve = solveZeroChar];
    $p = 0,
  (*else*)
    If[PrimeQ[p],
      $SNormal = PolynomialMod[#, p] &;
      $Solve = ModSolve;
      $p = p,
    (*else*)
      Message[FieldChar::prim, p];
      $Failed]]

FieldChar::prim = "Invalid field characteristic ``. It should be zero or a prime number."

If[$VersionNumber>=8,
ModSolve[eq_List, vars_List, elim_List, args___] :=
  With[{p = $p}, Solve[DeleteCases[Eliminate[Append[eq, Modulus == p],elim, Mode->Modular], Modulus == p], vars, args, Modulus -> p, Method->"Modular"] /.
      HoldPattern[Modulus -> p] -> Sequence[]];
ModSolve[eq_List, args___] :=
  With[{p = $p}, Solve[eq, args, Modulus -> p, Method->"Modular"] /.
      HoldPattern[Modulus -> p] -> Sequence[]],
(*else*)
ModSolve[eq_List, args___] :=
  With[{p = $p},
    Solve[Append[eq, Modulus == p], args, Mode -> Modular] /.
      HoldPattern[Modulus -> p] -> Sequence[]]]
ModSolve[eq_, args___] := ModSolve[{eq}, args]

$p = 0;

DivPowersQ[f_[___]] := DivPowersQ[f];
NewProperty[DivPowers];
DivPowersQ[_] = False;

DivPowersQ[a_,VPower] ^:= DivPowersQ[a]
DivPowers[a_->VPower] := DivPowers[a]
UnDivPowers[a_->VPower] := UnDivPowers[a]

DivPowersQ::mix = "Mixed ordinary and divided-power terms in ``"
DivPowersQ::parity = "Unable to expand divided power of ``: the parities of some terms are not known"
ExDivPowersQ[(SVTimes | VIf)[c_, e_]] := ExDivPowersQ[e]
ExDivPowersQ[VPower[e_, n_]] := ExDivPowersQ[e]
ExDivPowersQ[VTimes[]] := Null;
ExDivPowersQ[e : _VTimes | _VPlus] := DivPowersTermsQ[e];
ExDivPowersQ[e_] := DivPowersQ[e]

DivPowersTermsQ[e_] :=
  With[{r1=ExDivPowersQ[e[[1]]],r2=ExDivPowersQ[Rest[e]]},
    Which[
      r1===r2, r1,
      r1===Null, r2,
      r2===Null, r1,
      r1===$Failed || r2===$Failed, $Failed,
      True,  Message[DivPowersQ::mix,e]; $Failed;]]

ExpandDivPower[f_VPlus, n_] := VPlus @@
  Module[{base = List @@ f, pb=P/@base, degs},
    If[Select[pb,!NumberQ[P[#]]&,1]=!={},
      Message[DivPowersQ::parity, f];
      Return[f]];
    degs = LimCompositions[n, Table[If[pb[[i]]==0, n 1], {i,Length[base]}]];
    If [(Plus @@ pb) > 1,
      degs = Select[degs, (# . pb)<=1&]];
    Inner[VPower, base, #, VTimes] & /@ degs]

LimCompositions[0, m_List] := {Table[0, {Length[m]}]}

LimCompositions[n_Integer, m_List] :=
  Flatten[
    Table[
      Prepend[#, i] & /@ LimCompositions[n - i, Rest[m]],
      {i, Min[n, m[[1]]], Max[0, n - Plus @@ Rest[m]], -1}],
    1]

End[] (* =========== End of private code ============ *)


If[$VersionNumber>=3.0,
    Get["SuperLie`Format3`"],
    Get["SuperLie`Format2`"]
]

If[$FrontEnd=!=Null && Notebooks["SuperLie"]==={},
CreatePalette[{Cell[BoxData[
 ButtonBox["\<\"SuperLie Help\"\>",
  Appearance->Automatic,
  ButtonFunction:>FrontEndExecute[{
     FrontEnd`HelpBrowserLookup["RefGuide", 
      With[{$CellContext`nb = SelectedNotebook[]}, 
       SelectionMove[$CellContext`nb, All, Word]; ToString[
         NotebookRead[$CellContext`nb]]]]}],
  Evaluator->Automatic,
  Method->"Preemptive"]], NotebookDefault]},WindowTitle->"SuperLie"]]

Print["SuperLie Package Version 2.08 Beta 02 installed\nDisclaimer: This software is provided \"AS IS\", without a warranty of any kind"]

EndPackage[]

NewBracket[Act]
Jacobi[Act->CircleTimes]
Jacobi[Act->VTimes]

On[General::shdw, Remove::rmnsm]




