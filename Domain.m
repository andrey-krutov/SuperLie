(* ===== Domain.m =========================================== #)
>
>    The package for OBJECT ORIENTED programming
>
(# ========================================================== *)


BeginPackage["SuperLie`Domain`"]


(* #################   PART I. Tools. ##################### *)

SuperLie`Domain`SPrint::usage =
 "SPrint[format, val,..] = ToString[StringForm[...]]"
SPrint := Composition[ToString, StringForm]

SuperLie`Domain`AutoRule::usage =
 "AutoRule[rule] converts the replacement rule into definition, so the rule
will be automatically applied whenever possible. AutoRule[rule,tag]
attaches this definition to \"tag\"."

SuperLie`Domain`UnAutoRule::usage =
 "UnAutoRule[rule] cancels the definition(s) made by AutoRule[rule] or
AutoRule[rule,tag]."

SuperLie`Domain`NameSuffix::usage =
 "NameSuffix[name, \"suffix\"] builds new name, appending the suffix to 
the old name."

SuperLie`Domain`PrefixName::usage =
 "NameSuffix[\"prefix\", name] builds new name, prepending the prefix to
the old name."

SuperLie`Domain`ClearDef::usage =
 " ClearDef[def] clears all definitions matching the pattern def."

If [VersionNumber>=3.0,
 SuperLie`Domain`Tag::usage =
  "Tag[expr] returns the HoldPattern[tag], there \"tag\", is the first symbol
in the sequence \"expr, Head[expr], Head[Head[expr]], ... \". The head
of \"expr\" only is evaluated (as in left hand part of \"=\").";
 SuperLie`Domain`Target::usage =
  "Target[expr] returns the HoldPattern[value], there \"value\", is the given
expression \"expr\" with head and arguments evaluated (as in left hand
part of \"=\").",
(* else *)
 SuperLie`Domain`Tag::usage =
  "Tag[expr] returns the Literal[tag], there \"tag\", is the first symbol
in the sequence \"expr, Head[expr], Head[Head[expr]], ... \". The head
of \"expr\" only is evaluated (as in left hand part of \"=\").";
 SuperLie`Domain`Target::usage =
  "Target[expr] returns the Literal[value], there \"value\", is the given
expression \"expr\" with head and arguments evaluated (as in left hand
part of \"=\")."]

SuperLie`Domain`AddHead::usage =
  "AddHead[head,expr] adds header to the expression if Head[expr] =!= head.";

SuperLie`Domain`Prec::usage = SuperLie`Domain`Group::usage = SuperLie`Domain`Empty::usage = SuperLie`Domain`Type::usage =
SuperLie`Domain`InfixFormat::usage =
  "InfixFormat[sep][f]  define infix output format for \"f\":\n
  f[x1,x2,..] --> x1 sep x2 ... .\n
Options:\n
  Prec - precedence level (default 100);\n
  Empty - format for f[] (1);\n
  Type - format type (OutputForm).";

SuperLie`Domain`SetFormat::usage =
  "SetFormat[type, h, func] define the format of h[...] as func[h[...]]."

SuperLie`Domain`ClearFormat::usage =
  "ClearFormat[type, h] cancels the definition given by SetFormat."

SuperLie`Domain`SetToTag::usage =
  "SetToTag[symb] attaches assignments symb[arg,..] = ... to \"arg\"."

SuperLie`Domain`Compound::usage =
 "Compound[{proc,..}] converts the list of procedures with the same parameters
into compound procedure (proc[##];...)&."

SuperLie`Domain`JoinProperties::usage =
 "JoinProperties[lst1,..] joins the list of properties. From the properties
with the same name the first one is included."

SuperLie`Domain`UpdateProperties::usage =
 "UpdateProperties[{oldlist},{newvalues}] change the properties from oldlist to
newvalues ignoring the options missing in oldlist."

SuperLie`Domain`SymbolQ::usage =
 "SymbolQ gives True if expr is a symbol, and False otherwise."

(*Domain`Union::usage = System`Union::usage*)

SuperLie`Domain`DeleteSame::usage =
 "DeleteSame[h[arg..]] deletes the repeating consequent arguments.
DeleteSame[h[arg..], test] use test instead of SameQ for comparing arguments."

SuperLie`Domain`SameKeysQ::usage =
 "SameKeysQ[lft,rht] tests if the arguments are \"key\" or \"key->value\" with
the same key."

SuperLie`Domain`OrderedKeysQ::usage =
 "OrderedKeysQ[h[e1, e2, ...]] gives True if the keys of ei are in canonical 
order, and False otherwise."

SuperLie`Domain`OrderKeys::usage =
 "OrderKeys[expr1, expr2] gives 1 if the key of expr1 is before than the key of 
expr2 in canonical order, and -1 if expr1 is after expr2 in canonical order.
It gives 0 if the keys of expr1 and expr2 are identical."

SuperLie`Domain`SortKeys::usage =
 "SortKeys[list] sorts the elements of list into canonical order of keys."

SuperLie`Domain`UnionKeys::usage =
 "UnionKeys[list1, list2, ...] gives a sorted list of all elements with
distinct keys that appear in any of the listi. UnionKeys[list] gives a sorted
version of a list, in which all elements with duplicated keys have been
dropped."

SuperLie`Domain`ComplementKeys::usage =
 "ComplementKeys[list, list1, ...] gives a list of elements of list whose
keys does not that appear in any of the listi."

SuperLie`Domain`KeyValue::usage =
 "KeyValue[list,key] returns True if the list contains member key, the right
hand side of key->value if the list contains such member and False otherwise."

SuperLie`Domain`MergeLists::usage =
 "MergeLists[list,...,option...] returns the merged list. Options are:
Sort->p defines the predicate for Sort function, SameTest->fn gives a test
for merging, and Merge->fn defines the merging function"

If [$VersionNumber < 10, Symbol["SuperLie`Domain`Merge"]]

(* ---------------  AttributeQ  ------------------- *)


dmn`attruse = "`1`Q[symb] gives True if \"symb\" has attribute \"`1`\",
and False otherwise."


SuperLie`Domain`AttributeQ::usage =
 "AttributeQ[symb, attr] gives True if \"symb\" has the attribute \"attr\",
and False otherwise."
AttributeQ =	MemberQ[Attributes[#1], #2]&

SuperLie`Domain`ConstantQ::usage = SPrint[dmn`attruse, Constant]
ConstantQ =	MemberQ[Attributes[#], Constant]&

SuperLie`Domain`HoldAllQ::usage = SPrint[dmn`attruse, HoldAll]
HoldAllQ =	MemberQ[Attributes[#], HoldAll]&

SuperLie`Domain`HoldFirstQ::usage = SPrint[dmn`attruse, "HoldFirst\" or \"HoldAll"]
HoldFirstQ =	MemberQ[Attributes[#], HoldFirst|HoldAll]&

SuperLie`Domain`HoldRestQ::usage = SPrint[dmn`attruse, "HoldFirst\" or \"HoldRest"]
HoldRestQ =	MemberQ[Attributes[#], HoldRest|HoldAll]&

SuperLie`Domain`ListableQ::usage = SPrint[dmn`attruse, Listable]
ListableQ =	MemberQ[Attributes[#], Listable]&

SuperLie`Domain`LockedQ::usage = SPrint[dmn`attruse, Locked]
LockedQ =	MemberQ[Attributes[#], Locked]&

SuperLie`Domain`OneIdentityQ::usage = SPrint[dmn`attruse, OneIdentity]
OneIdentityQ =	MemberQ[Attributes[#], OneIdentity]&

SuperLie`Domain`OrderlessQ::usage = SPrint[dmn`attruse, Orderless]
OrderlessQ =	MemberQ[Attributes[#], Orderless]&

SuperLie`Domain`ProtectedQ::usage = SPrint[dmn`attruse, Protected]
ProtectedQ =	MemberQ[Attributes[#], Protected]&

SuperLie`Domain`ReadProtectedQ::usage = SPrint[dmn`attruse, ReadProtected]
ReadProtectedQ =MemberQ[Attributes[#], ReadProtected]&

SuperLie`Domain`StubQ::usage = SPrint[dmn`attruse, Stub]
StubQ =		MemberQ[Attributes[#], Stub]&

SuperLie`Domain`TemporaryQ::usage = SPrint[dmn`attruse, Temporary]
TemporaryQ =	MemberQ[Attributes[#], Temporary]&



Begin["dmn`"] (* ==================== Private ======================= *)


(* ----------- AutoRule ---------- UnAutoRule ----------------- #)
>  AutoRule[rule] transform a replacement rule into a definition.
>  AutoRule[rule,tag] attaches this definition to 'tag'
>  UnAutoRule[rule] cancels this definition.
(# ------------------------------------------------------------ *)

Attributes[AutoRule] = {HoldFirst}
Attributes[UnAutoRule] = {HoldFirst}

SavedRules = {}

AutoRule::reps = UnAutoRule::reps = "{``} is not list of replacement rules."
AutoRule::dupl = "Auto Rule \"``\" was already defined."

UnAutoRule::notfound = "Auto Rule \"``\" not found."

(*
FindIf[predicat_, list_] := 
 With[{sel=Select[list, predicat, 1},
  If[Length[sel]>0, First[sel]]]
*)

AutoRule[rule_, tag_:None] :=
Module[{target, hold},
  target = Target[rule];
(*  If [MemberQ[SavedRules, {target,__}], *)
  If[Select[SavedRules, First[#]===target&, 1]=!={},
  (*then*)
     Message[AutoRule::dupl, HoldForm[rule]]; {},
  (*else*)
    ARres = {};
    hold = Hold[Evaluate[rule]];
    AutoRuleScan[rule, tag];
    AppendTo[SavedRules, {target, hold,
	If[tag===None, Unset, TagUnset[tag,#]&], Flatten[ARres]}];
    If [ !ProtectedQ[Tag[rule]], rule = {} ];
  {HoldForm @@ target}
  ]
]

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 AutoRuleScan[rule_, None] :=
  Switch[ Head[rule],
    Rule,		ARres = { ARres, AddHead[wrapper,rule[[1]]] }; 
			Set @@ rule,
    RuleDelayed,	ARres = { ARres, AddHead[wrapper,rule[[1]]] }; 
			SetDelayed @@ rule,
    List,		Scan[AutoRuleScan[#,None]&, rule],
    _,			Message[AutoRule::reps, rule]
  ];
 AutoRuleScan[rule_, tag_] :=
  Switch[ Head[rule],
    Rule,		ARres = { ARres, AddHead[wrapper,rule[[1]]] };
			TagSet[tag,##]& @@ rule,
    RuleDelayed,	ARres = { ARres, AddHead[wrapper,rule[[1]]] };
			Replace[rule, (a_:>b_):>(tag/:a:=b)],
			(*TagSetDelayed[tag,##]& @@ rule,*)
    List,		Scan[AutoRuleScan[#,tag]&, rule],
    _,			Message[AutoRule::reps, rule]
  ]
]

UnAutoRule[rule_] := 
  Module[{sv, target},
    target = Target[rule];
(*    sv = Cases[SavedRules, {target,__}]; *)
    sv = Select[SavedRules, First[#]===target&, 1];
    If [Length[sv]==0,
     (*then*)
	Message[UnAutoRule::notfound, HoldForm[rule]]; {},
     (*else*)
	sv = sv[[1]];
	sv[[3]] /@ Reverse[sv[[4]]];
	If [!ProtectedQ[Tag[rule]], rule =. ;
	   If [sv[[2,1]]=!=rule,  rule = sv[[2,1]] ];
	]
    ];
(*    SavedRules = DeleteCases[SavedRules, {target,__}]; *)
    SavedRules = Select[SavedRules, First[#]=!=target&];
  {HoldForm @@ target}
  ]

(* ---------- PrefixName ------ NameSuffix ------------- *)

NameSuffix[name_, suffix_] := ToExpression[ToString[name]<>suffix]

PrefixName[prefix_, name_] := ToExpression[prefix<>ToString[name]]

(* ----------------- Tag ------------------- *)


(*Attributes[Tag] = {HoldAll} *)

(* Tag[Literal[expr_]] := Tag[expr] *)
(*
With[{wrapper = If[$VersionNumber >= 3.0, HoldPattern, Literal]},
  Tag[(x : (wrapper|Blank|BlankSequence|BlankNullSequence|Repeated|RepeatedNull))[expr_]] := Tag[expr];
  Tag[(a : Pattern)[_, x_]] := Tag[x];
  Tag[x_[___]] := Tag[x];
  Tag[x_Symbol] := wrapper[x]
]
*)

Attributes[Tag] = {HoldFirst}

Tag[x_]:=Tag[x,If[$VersionNumber >= 3.0, HoldPattern, Literal]]
Tag[(x : (HoldPattern|Literal|Blank|BlankSequence|BlankNullSequence|Repeated|RepeatedNull))[expr_],
      wrapper_] := Tag[expr,wrapper];
Tag[(a : Pattern)[_, x_],wrapper_] := Tag[x,wrapper];
Tag[x_[___],wrapper_] := Tag[x,wrapper];
Tag[x_Symbol,wrapper_] := wrapper[x]


(* ----------------- ClearDef ------------------- *)

Attributes[ClearDef] = {HoldAll}
Attributes[ClearSet] = {HoldAll}
(*
ClearSet[tag_, def_] := 
  With[{val = Hold /@ Apply[Sequence,
	ToHeldExpression[ToString[ InputForm[Definition[tag]] ]], {1}]},
   Clear[tag];
   CompoundExpression @@ Apply[Sequence, DeleteCases[val, Hold[def]], {1}]
  ]

ClearDef[def:(Set|SetDelayed)[lhs_,rhs_]] :=
	With[{tag=Tag[lhs][[1]]}, ClearSet[ tag, def ] ]

ClearDef[def:(UpSet|UpSetDelayed)[lhs_,rhs_]] :=
 ((With[{tag=Tag[#][[1]]},
     If [SymbolQ[tag] && !ProtectedQ[tag], ClearSet[ tag, def ] ]
   ] )& /@ (List@@lhs);)

ClearDef[def:(TagSet|TagSetDelayed)[tag_,___]] := ClearSet[ tag, def ]
*)

ClearDef[def:(Set|SetDelayed)[lhs_,rhs_]] :=
   With[{tag=Tag[lhs][[1]],pat=AddHead[HoldPattern,Unevaluated[lhs]]},
    ClearSet[ tag, pat:>rhs ] ]

ClearDef[def:(UpSet|UpSetDelayed)[lhs_,rhs_]] :=
 With[{pat=AddHead[HoldPattern,Unevaluated[lhs]]},
  (With[{tag=Tag[#][[1]]},
     If [SymbolQ[tag] && !ProtectedQ[tag], ClearSet[ tag, pat:>rhs ] ]
   ] )& /@ (List@@lhs);]

ClearDef[def:(TagSet|TagSetDelayed)[tag_,rhs_,lhs_]] :=
   With[{pat=AddHead[HoldPattern,Unevaluated[lhs]]}, ClearSet[ tag, pat:>rhs ] ]

ClearSet[tag_,rule_]:=
  (#[tag]=Select[#[tag],DiffPattern[rule]])& /@ {OwnValues,DownValues,UpValues,FormatValues}

ClearDef[v1_, v2__] := ClearDef /@ Unevaluated[CompoundExpression[v1,v2]];

ClearDef[v_] := Clear[v] /; SymbolQ[v]

ClearDef[v_] :=
   With[{tag=Tag[v][[1]],pat=AddHead[HoldPattern,Unevaluated[v]]},
     (#[tag]=Select[#[tag],DiffTarget[pat]])& /@ {OwnValues,DownValues,UpValues,FormatValues}]


SamePattern[f_, g_] :=
    Catch[Block[{eqpat = {}}, SamePat[f, g]; True], SamePattern];

DiffPattern[f_] := (!SamePattern[f,#]&)
DiffTarget[f_] := (!SamePattern[f,#[[1]]]&)

Attributes[SamePat] = {HoldAll}

SamePat[f_, g_] :=
    Which[
      AtomQ[Unevaluated[f]],
        If[Unevaluated[f] =!= Unevaluated[g], Throw[False, SamePattern]],
      Head[Unevaluated[f]] =!= Head[Unevaluated[g]] || Length[Unevaluated[f]] != Length[Unevaluated[g]],
        Throw[False, SamePattern],
      Head[Unevaluated[f]] === Pattern, 
        If[f[[2]] =!= g[[2]] || DifPat[f[[1]], g[[1]]], Throw[False, dmn`SamePattern]],
      True,
        Inner[SamePat, Unevaluated[f], Unevaluated[g], CompoundExpression]];

DifPat[a_, b_] :=
  Which[
    Cases[eqpat, {a, b}] =!= {}, False,
    Cases[eqpat, {a, _}] =!= {}, True,
    Cases[eqpat, {_, b}] =!= {}, True,
    True, AppendTo[eqpat, {a, b}]; False]

(* ----------------- Target ------------------- *)

Attributes[Target] = {HoldAll}

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 Target[expr_, wrap_:wrapper] :=
  Module[{ret, len, i},
   len = Length[Unevaluated[expr]];
   ret = wrap[expr];
   If [len>0, For [i=0, i<=len, ++i,
	ret = ReplacePart[ret, ret[[1,i]], {1, i}] ]
  ];
  ret
 ]
]

(* ----------------- AddHead ------------------- *)

AddHead[head_, expr:head_[___]] := expr
AddHead[head_, expr_] := head[expr]


(* -------------------- InfixFormat ------------------------- #)
>
>  InfixFormat[sep]  define infix output format for "f": 
>	f[x1,x2,..] --> x1 sep x2 ... 
>  Options:
>    Prec - precedence level	(default 100);
>    Empty - format for f[] 	(1);
>    Type - format type 	(OutputForm).
>
(# ---------------------------------------------------------- *)

Options[InfixFormat] ^=
	{ Prec->100, Empty->"1", Type->OutputForm };

InfixFormat[sep_, opts___] :=
(   Switch[Length[#],
	0, Empty,
	1, First[#],
	_, Infix[PrecedenceForm[#,Prec]&/@ #, sep]
    ]
) & /. Join[{opts}, Options[InfixFormat]]

(* ----------------- SetToTag ------------------- *)

Attributes[DownTag] = {HoldAll}
DownTag[expr_] := Tag @@ HeldPart[Unevaluated[expr], 1]

SetToTag[symb_Symbol] :=
( symb /: Set[expr_symb, val_] := TagSet[Evaluate[DownTag[expr][[1]]], expr, val];
  symb /: SetDelayed[expr_symb, val_] := TagSetDelayed[Evaluate[DownTag[expr][[1]]], expr, val];
  symb /: UpSet[expr_symb, val_] := TagSet[Evaluate[DownTag[expr][[1]]], expr, val];
  symb /: UpSetDelayed[expr_symb, val_] := TagSetDelayed[Evaluate[DownTag[expr][[1]]], expr, val];
  symb /: Unset[expr_symb] := TagUnset[Evaluate[DownTag[expr][[1]]], expr];
)


UpdateProperties[old_List, new_List] :=
 Module[ { oli, lpos },
   (    oli = #;
	If [ Head[oli]===Rule, oli = First[oli] ];
	lpos = Position[new, oli | (oli->_), {1} ];
	If [ lpos==={}, #, new[[ lpos[[-1,1]] ]] ]
   )& /@ old
 ]
	
(* ---------  PROPERTY : Symbol -------------- *)

SymbolQ[_Symbol] = True
SymbolQ[_] = False

(* --------- Union: user sorting ------------- *)

Options[SuperLie`Domain`Union] = { SameTest -> Automatic, Sort->Automatic }

DeleteSame[h_[], ___] := h[]

DeleteSame[expr_, test_:SameQ] :=
 Module[{x,y={expr[[1]]}},
   (x=y; y=#; If[test[x,y], Unevaluated[], y])& /@ expr
 ]


Union[args__,opts___Rule] :=
 Module[{same, sort},
   {same, sort} = {SameTest,Sort} /. {opts} /. Options[Union];
   If [ same===Automatic, same = Unevaluated[] ];
   If [ sort===Automatic, sort = Unevaluated[] ];
   DeleteSame[ Sort[Join[args], sort], same]
 ]

MergeLists[e___List,opts___Rule]:=
  With[{sort=Sort/.{opts}/.Options[MergeLists]/.Automatic->Unevaluated[],
        same=SameTest/.{opts}/.Options[MergeLists]/.Automatic->Unevaluated[],
	merge=Merge/.{opts}/.Options[MergeLists]},
    Apply[merge, Split[Sort[Join[e],sort],same], {1}]]

Options[MergeLists]^={Sort->Automatic,SameTest->Automatic,Merge->(#1&)}

(* --------------- Sort keys --------------------- *)

OrderedKeysQ[h_[args___]] := OrderedQ[{args}/.(a_->_):>a]

SameKeysQ[lkey_->_,rkey_->_] := SameQ[lkey,rkey]
SameKeysQ[lkey_->_,rkey_] := SameQ[lkey,rkey]
SameKeysQ[lkey_,rkey_->_] := SameQ[lkey,rkey]
SameKeysQ[lkey_,rkey_] := SameQ[lkey,rkey]

OrderKeys[lkey_->_,rkey_->_] := Order[lkey,rkey]
OrderKeys[lkey_->_,rkey_] := Order[lkey,rkey]
OrderKeys[lkey_,rkey_->_] := Order[lkey,rkey]
OrderKeys[lkey_,rkey_] := Order[lkey,rkey]

SortKeys[lst_] := Sort[lst, OrderedKeysQ[{#1,#2}]&]
UnionKeys[lst__] := Union[lst, SameTest -> SameKeysQ,
	Sort -> (OrderedKeysQ[{#1,#2}]&)]
ComplementKeys[lst__] := Complement[lst, SameTest -> SameKeysQ]


KeyValue[{___,key_,___}, key_, default_:False] := True
KeyValue[{___,key_->value_,___}, key_, default_:False] := value
expr:KeyValue[lst_, _, default_:False] := default /; ListQ[lst] ||
	 (Message[KeyValue::list, HoldForm[expr], 1]; default);

End[]  (* =================================================== *)


(* #################  PART II.  Domains  ################### *)

Domain::usage =
 "Domain[expr] returns the domain of the value of \"expr\". Domain[op, n, tot]
returns the domain of \"n\"-th argument of \"op\" with \"tot\" arguments.
Domain[op, First], Domain[op, Last] and Domain[op, All] return the domain of
the respective argument of \"op\" arguments."

NewProperty::usage =
  "NewProperty[name] declares new property. NewProperty[name, {method,..}]
describes also the method of set/reset of the property."

Flag::usage = FlagMethod::usage =
 "Flag is the default method of declaring the property of on object."

Flags::usage =
 "Flags[obj] returns the list of flags, associated with the object."

RuleMethod::usage = "Rule is a method of declaring the property of an object."

TagRuleMethod::usage = "TagRule is a method of declaring the property of an object."

Rules::usage =
 "Rules[obj] returns the list of rules, associated with the object."

VarRule::usage = VarRuleMethod::usage = 
 "VarRule is a method of declaring the property of on object."

Also::usage = AlsoMethod::usage =
 "Also is a method of declaring the property of on object."

Option::usage = OptionMethod::usage = 
 "Option is a the method of declaring the property of on object."

DomainMethod::usage =
 "Domain is a the method of declaring the property that the object belong
to the domain."

FormatMethod::usage =
 "Format is the method of declaring output properties of objects."

Formats::usage =
 "Formats[obj] returns the list of input/output formats, associated with the object."

NewValue::usage =
 "NewValue[val,..] declares new properties of the type Value."

ListValues::usage =
 "ListValues[obj] returns the list of values, associated with the object."

NewList::usage =
 "NewList[name,..] declares new properties of the type ValueList."

NewDomain::usage =
  "NewDomain[name] declares new domain. NewDomain[name, {method..}, \"prefix\"]
describes also the method of creating/deleting of the objects and the
prefix for the rules in this domain."

Define::usage =
 "Define[obj, domain] defines new object or list of objects. Define[obj,
{domain, property,..}] defines the object with given properties."

SetProperties::usage =
 "SetProperties[obj, prop] declares the property (or list of properties) of the
object (or list of objects). Property must be either symbol or option-like:
\"symb\" or \"symb->parm\" or \"symb->{parm,..}\"."

ClearProperties::usage =
 "ClearProperties[obj, prop] cancels the declarations of SetProperties." 

Alpha::usage =
 "Alpha is the domain of the character strings. Alpha[symb, ..] is the
constructor of Alpha objects."
UnAlpha::usage = "UnAlpha[obj,..] is the destructor of Alpha objects."
AlphaQ::usage = "AlphaQ[x] returns True if x is an object of Alpha domain."

Scalar::usage = 
 "Scalar is the domain of the numbers and scalar variables. Scalar[obj,..] is
the constructor of Scalar objects."
UnScalar::usage = "UnScalar[obj,..] is the destructor of Scalar objects."
ScalarQ::usage = "ScalarQ[x] returns True if x is an object of Scalar domain."

Common::usage = CommonQ::usage = "Common is the default domain."

Operation::usage =
  "Operation[name, generic[domain..]->domain, ] defines new operation as
restriction of the \"generic\" operation to given domains."


About::usage = $AboutList::usage =
 "About[obj] prints the information about the object. About[obj,{topics}]
specified the list of topics to be printed. $AboutList is the default
list of topics."

Begin["dmn`"] (* ================================================== *)

(* ----------------- Domain ------------------ *)

Domain[x_Symbol] := 
  Switch[Context[x],
    "System`",  If[ MemberQ[Attributes[x], Constant], Scalar, Common],
    "Global`",  Common,
    _,		Message[Domain::undef, x]; Void
  ]

Domain[_?NumberQ] := Scalar

Domain[_String] := Alpha

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
  Domain[wrapper[x_]] := Domain[Unevaluated[x]]
]

Domain[x_] := Domain[Head[x]]

Domain[x_, i_, i_] := Domain[x,Last]
Domain[x_, 1, _] := Domain[x,First]
Domain[x_, _, _] := Domain[x,All]

(* See also the definitions for particulars object *)


(* -------------------  About --------------------- *)

$AboutList :=
  { Domain, Attributes, Options, Flags, ListValues, Rules, Formats }
(*
expr:About[obj_,topics_:$AboutList] :=
With[{opt = Options[#, FormatType]& /@ $Output },
  SetOptions[$Output, FormatType -> TextForm];
  If [ValueQ[obj::usage], Print[obj::usage] ];
  With[{res = #[obj]}, If [Head[res]=!=# && res=!={},
				Print[#, ": ", TextForm[res]] ]]&  /@  topics;
  Inner[SetOptions, $Output, opt, CompoundExpression];
] /; ( SymbolQ[obj] || (Message[About::sym, obj, 1]; False) ) &&
     ( ListQ[topics] || (Message[About::list, Unevaluated[expr], 2]; False) )
*)
expr:About[obj_,topics_:$AboutList] :=
(
  If [ValueQ[obj::usage], Print[obj::usage] ];
  With[{res = #[obj]}, If [Head[res]=!=# && res=!={},
				Print[#, ": ", res] ]]&  /@  topics;
) /; ( SymbolQ[obj] || (Message[About::sym, obj, 1]; False) ) &&
     ( ListQ[topics] || (Message[About::list, Unevaluated[expr], 2]; False) )

(* ----------------- NewProperty ------------------ *)

FlagMethod[name_, val_] :=
( AppendTo[ FlagsList, name];
   With[{nmQ=NameSuffix[name,"Q"]},
	nmQ[obj_?AtomQ] := False;
	nmQ[obj_] := nmQ[Head[obj]];
	{ (#1/: nmQ[#1] := val)&,
	  (#1/: nmQ[#1] =.)& }
  ]
)

FlagMethod[name_] :=
( AppendTo[ FlagsList, name];
   With[{nmQ=NameSuffix[name,"Q"]},
	nmQ[obj_?AtomQ,___] := False;
	nmQ[obj_,args___] := nmQ[Head[obj],args];
	{ setFlag[nmQ,##]&, clearFlag[nmQ,##]& }
  ]
)

setFlag[fn_,var_,{args___}] := setFlag[fn,var,args];
setFlag[fn_,var_,args___] := (var/:fn[var,args]=True);

clearFlag[fn_,var_,{args___}] := clearFlag[fn,var,args];
clearFlag[fn_,var_,args___] := (var/:fn[var,args]=.);


Flags[obj_] :=
  Flatten[
    With[{test = NameSuffix[#1, "Q"], o = obj},
      ConvFlags /@
        Cases[UpValues[o] /. HoldPattern -> Hold,
          HoldPattern[Hold[test[o, ___]] :> True]]] & /@ FlagsList]

ConvFlags[Hold[flag_[_]] :> True] := flag;
ConvFlags[Hold[flag_[_, a_]] :> True] := (flag -> a);
ConvFlags[Hold[flag_[_, a__]] :> True] := (flag -> {a});

FlagsList = {}

RuleMethod[name_, parm___] :=
 With [{nmRule=NameSuffix[name, "Rule"]},
	{ (Rules[#1] ^= Union [ Rules[#1], AutoRule[nmRule[##,parm]] ]) &,
   (Rules[#1] ^= Complement[ Rules[#1], UnAutoRule[nmRule[##,parm]] ]) &
 }
]

TagRuleMethod[name_, parm___] :=
 With [{nmRule=NameSuffix[name, "Rule"]},
	{ (Rules[#2] ^= Union [ Rules[#2], AutoRule[nmRule[##,parm],#2] ]) &,
   (Rules[#2] ^= Complement[ Rules[#2], UnAutoRule[nmRule[##,parm]] ]) &
 }
]

Rules[_] := {}

AlsoMethod[_, name_List] := Compound /@ Transpose [ AlsoMethod[0, #]& /@ name ];

AlsoMethod[_, name_] :=
  With [ {unname = PrefixName["Un",name] }, { name[##]&, unname[##]& } ];

AlsoMethod[_, name_->parm_] :=
  With [ {unname = PrefixName["Un",name] },
		{ name[#->parm]&, unname[#->parm]& }
  ]

VarRuleMethod[name_, parm___] :=
  With [{nmRule=NameSuffix[name, "Rule"]},
    { VarApply[AutoRule, nmRule, ##, parm]&,
      VarApply[UnAutoRule, nmRule, ##, parm]& }
  ]

VarApply[func_, name_, obj_, parm___] :=
  With[ { name = PrefixName[ DomainPrefix[Domain[obj]], name] },
	func [ name[obj, parm] ]
  ]

DomainMethod[name_] := { ( #1/: Domain[##] = name )&, ( #1/: Domain[##] =. )& }

DomainPrefix[_] = "";

OptionMethod[name_, val_:True] :=
  { AddOption[name, ##, val]&, DelOption[name, #1]& }

AddOption[opt_, obj_, val_, ___] :=
  ( Options[obj] ^= UnionKeys[ {opt->val}, Options[obj] ] )

DelOption[opt_, obj_] := (Options[obj] = DeleteCases[Options[obj], opt->_];)

FormatMethod[name_, val___] :=
  { SetFormat[ NameSuffix[name,"Form"], #1, ##2, val] &,
    ClearFormat[NameSuffix[name,"Form"], #1]&
  }

(*FormatFn[h_,type_] := KeyValue[Formats[h],type,None];*)
Formats[_] := {};

SetFormat[type_, h_, None] := ClearFormat[type,h];

SetFormat[type_, h_, func_] := (
   ClearFormat[type,h];
   If[type===StandardForm,
      SetInputFormat[h,func];
      SetOutputFormat[h,func],
  (*else*)
      h/:Format[e_h,type] := func[e]];
   Formats[h] ^= UnionKeys [ Formats[h], {type->func}]
   (*FormatFn[h,type] = func*)
    )

SetInputFormat[h_, func_] := Null

SetInputFormat[h_, Subscripted] := 
  With[{t = ToString[h]}, SubsctiptToArg[t]=True]

SetOutputFormat[h_,func_] := (h/:Format[e_h,StandardForm]:=func[e])
(*SetOutputFormat[h_, Subscripted] := (h/:MakeBoxes[e_h,StandardForm]:=SubscriptBox[h,MakeRowBox@@e,StandardForm])*)
SetOutputFormat[h_, Subscripted] := (h/:MakeBoxes[e_h,StandardForm]:=SubscriptBox[MakeBoxes[h,StandardForm],MakeRowBox@@e])

MakeRowBox[x_]:=MakeBoxes[x,StandardForm];
MakeRowBox[x_,y__]:=RowBox[Flatten[{MakeBoxes[x,StandardForm],({",",MakeBoxes[#,StandardForm]}&)/@{y}}]]

ClearFormat[type_,h_] := 
   With[{old=KeyValue[Formats[h],type,None]},
     If[old=!=None,
       FormatValues[h] = Select[FormatValues[h],DiffTarget[HoldPattern[Format[e_h,type]]]];
       If[type===OutputForm,
         FormatValues[h] = Select[FormatValues[h],DiffTarget[HoldPattern[Format[e_h]]]],
         FormatValues[h] = Select[FormatValues[h],DiffTarget[HoldPattern[MakeBoxes[e_h,type]]]]];
       If[type===StandardForm, ClearInputFormat[h,old]];
       Formats[h] ^= ComplementKeys[Formats[h],{type}]
       (*FormatFn[h,type]=.*)
       ]]

ClearInputFormat[h_, func_] := Null

ClearInputFormat[h_, Subscripted] := 
  With[{t = ToString[h]}, SubsctiptToArg[t] =.]

MakeExpression[SubscriptBox[base_, sub_], StandardForm] :=
  MakeExpression[RowBox[{base, "[", sub, "]"}]] /; SubsctiptToArg[base]

SubsctiptToArg[base_] = False;

Method$[a_->val_] := Method$[a][#,val]&
Method$[a_] := NameSuffix[a,"Method"]

Compound[{func_}] := func
Compound[{func___}] :=
	Distribute[{func}, Function, List, Function, CompoundExpression]

(*
NewProperty[name_, method_:{Flag}] :=
 Module[ {constr, destr },
  Off[General::spell1];
  { constr, destr } = Transpose[ Method$[#][name]& /@ method ];
  NewConstructor[ name, Compound[constr] ];
  NewConstructor[ PrefixName["Un",name], Compound[destr] ];
  On[General::spell1];
]
*)

NewProperty[name_, method_:Flag, default_:True] :=
  Module[{constr, destr, meth},
    meth = Which[method === Null, {Flag}, ListQ[method], method, True, {method}];
    Off[General::spell1];
    {constr, destr} = Transpose[Method$[#][name] & /@ meth];
    NewConstructor[name, Compound[constr], default];
    NewConstructor[PrefixName["Un", name], Compound[destr], default];
    On[General::spell1];]

NewValue[name__] :=
 Scan[ Function [{nm}, AppendTo[ValuesList, nm];
	nm[obj_->val_,parm___] := (nm[obj] ^= val; nm[parm]);
	nm[] := Null;
	NewConstructor[ PrefixName["Un",nm], (#/: nm[#]=.)& ] ],
   {name}
 ]

ValuesList = {}

With[{wrapper=If[$VersionNumber>=3.0, HoldPattern, Literal]},
 ListValues[obj_] :=
  With[{val= wrapper[#[obj]]/.UpValues[obj]},
    If [val=!=wrapper[#[obj]], #->val[[1]], Unevaluated[]]
  ]& /@ ValuesList
]

NewList[name_] :=
( AppendTo[$AboutList, name];
  name[obj_->val_, args___] :=
    ( name[obj] ^= UnionKeys[ AddHead[List,val], name[obj] ]; name[args] );
  name[obj_, key_] := KeyValue[ name[obj], key ];
  name[] := Null;
  With[ {unname = PrefixName["Un",name]},
	unname[obj_->val_List, args___] := ( unname[args]; name[obj] ^=
		Complement[name[obj], AddHead[List,val], SameTest->SameKeysQ];);
  ];
  name[_] = {};
)

NewConstructor[name_, constr_] :=
( name[obj_] := constr[obj];
  name[obj_->prm_] := constr[obj, prm];
  name[obj_,objs__] := Scan[name, {obj, objs}];
)

NewConstructor[name_, constr_, default_] :=
  With[{con1 = constr /. #2 -> default},
    name[obj_] := con1[obj];
    name[obj_ -> prm_] := constr[obj, prm];
    name[obj_, objs__] := Scan[name, {obj, objs}]]


(* ----------------- NewDomain ------------------ *)

NewDomain[name_, method_:{Flag}, prefix_:""] :=
( DomainPrefix[name] ^= prefix;
  Domain[name] ^= Domain;
  NewProperty[ name, Append[method, Domain] ];
)

(* ---------------  Set/Cancel Property  ------------------- *)

SetProperties[obj_, prop_, more__]	:= Scan[ SetProperties[obj,#]&, {prop,more}]
SetProperties[obj_, prop_List]		:= Scan[ SetProperties[obj,#]&,  prop]
SetProperties[obj_List, prop_->parm_]	:= prop @@ (#->parm&) /@ obj
SetProperties[obj_List, prop_]		:= prop @@ obj
SetProperties[obj_, prop_->parm_]	:= prop @ (obj->parm)
SetProperties[obj_, prop_]		:= prop @ obj
SetProperties[obj_, Attributes->list_]	:= SetAttributes[obj,list]

ClearProperties[obj_, prop_, more__]    := Scan[ ClearProperties[obj,#]&,  {prop,more}]
ClearProperties[obj_, prop_List]        := Scan[ ClearProperties[obj,#]&,  prop]
ClearProperties[obj_List, prop_->parm_] :=
				PrefixName["Un",prop] @@ (#->parm&) /@ obj
ClearProperties[obj_List, prop_]    := PrefixName["Un",prop] @@ obj
ClearProperties[obj_, prop_->parm_] := PrefixName["Un",prop] @ (obj->parm)
ClearProperties[obj_, prop_]	    := PrefixName["Un",prop] @ obj
ClearProperties[obj_, Attributes->list_] := ClearAttributes[obj,list]


(* ---------------  Define  ------------------- *)

Define[obj_List, prop__] := Scan[Define[#, prop]&, obj]

Define[obj_, prop__] :=
 ( ClearAll[obj];
   SetProperties[obj, prop]
) /; SymbolQ[Unevaluated[obj]] ||
	(Message[Define::sym, Unevaluated[obj], 1]; False)

(* ---------- Built-in domain: Alpha -------------- *)

NewDomain[Alpha]
Domain[_String] := Alpha
Clear[AlphaQ];
AlphaQ[x_] := (Head[x]===String)


(* ---------- Built-in domain: Scalar ------------- *)

Domain[_?NumberQ] := Scalar
ScalarQ[_?NumberQ] := True
ScalarQ[x_Symbol] := ConstantQ[x]
NewDomain[ Scalar, {Flag}, "S" ]


(* ---------- Operation --------------- *)

Attributes[Operation] = {HoldRest}

Operation[name_, gen_[arg___]->res_] :=
 ( SetDelayed @@
   (HoldForm @@ { Hold[gen] [ MapIndexed[ArgCond, Unevaluated[arg,Null]] ],
		   Hold[name][ MapIndexed[ArgRepl, Unevaluated[arg,Null]] ]
		}  /. Hold[x_]:>x
   );
   argCnt = 0;
   argTot = Length[{arg}];
   Do [ArgDomain[name, {arg}[[i]] ], {i, argTot}];
   res[name]
 )

ArgCond[dm_Repeated, {i_}] := 
	ToExpression[ToString[StringForm["x``__?``Q", i, First[dm] ]]]
ArgCond[dm_RepeatedNull, {i_}] :=
	ToExpression[ToString[StringForm["x``___?``Q", i, First[dm] ]]]
ArgCond[dm_Rule, ind_] := ArgCond[First[dm], ind];
ArgCond[Null, {i_}] := Unevaluated[]
ArgCond[domn_, {i_}] :=
	ToExpression[ToString[StringForm["x``_?``Q", i, domn]]]

ArgRepl[_->op_, {i_}] := Hold[op][PrefixName["x",i]];
ArgRepl[Null, {i_}] := Unevaluated[]
ArgRepl[_, {i_}] := PrefixName["x",i];


ArgDomain[name_, _->op_] := ArgDomain[name, Domain[op]]

ArgDomain[name_, dm_Repeated|_RepeatedNull] :=
( argCnt -= argTot-1;
  name/: Domain[name, _, _] = First[dm]
)

ArgDomain[name_, domn_] :=
   If [argCnt>=0, name/: Domain[name, ++argCnt, _] = domn,
	(*else*)  name/: Domain[name, n_-(++argCnt), n_] = domn
   ];


Remove[Domain] ^:= 
( Remove["SuperLie`Domain`*", "dmn`*"];
  $ContextPath = DeleteCases[$ContextPath, "SuperLie`Domain`"];
(*  $Packages = DeleteCases[$Packages, "Domain`"]; *)
)

End[]
EndPackage[]
