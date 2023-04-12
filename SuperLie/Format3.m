SuperLie`PreSL::usage =
 "PreSL is a preprocessor function what interprets the user input 
in SuperLie package. Use $Pre=. and $Pre=PreSL to turn the preprocessing
off and on."

SuperLie`WithoutPreSL::usage =
 "Use WithoutPreSL[expr,...] to prevent preprocessing of expressions when
the preprocessing is turned on."

SuperLie`Plus$::usage = "Plus$ is equivalent to WithoutPreSL[Plus]"
SuperLie`Times$::usage = "Times$ is equivalent to WithoutPreSL[Times]"
SuperLie`Power$::usage = "Power$ is equivalent to WithoutPreSL[Power]"

SuperLie`NewPower::usage =
 "NewPower[power, symbol, texsymbol] defines a new power operation
(for an existing times-type operation) with the input/output format
\"a^symbol b\" or \!\(a\^\(symbol\ b\)\)."

SuperLie`RemovePower::usage =
 "RemovePower[power] cancels the power operation defined with NewPower."

SuperLie`NewSuperscript::usage =
 "NewSuperscript[op, symb] defines new operation op[x] with superscript
standard format \!\(x\^\(symb\)\). NewSuperscript[op, symb, tex] defines
also TeX format x^{tex}."

SuperLie`RemoveSuperscript::usage =
 "RemoveSuperscript[op] cancels the superscript format for operation op
defined with NewSuperscript."

SuperLie`NewOverscript::usage =
 "NewOverscript[op, symb] defines new operation op[x] with overscript
standard format \!\(x\&symb\). NewOverscript[op, symb, tex] defines
also TeX format x^{tex}."

SuperLie`RemoveOverscript::usage =
 "RemoveOverscript[op] cancels the overscript format for operation op
defined with NewOverscript."

SuperLie`UseAsSymbol::usage =
 "UseAsSymbol[expr] tells Mathematica to treate the given expression as
a single symbol. UseAsSymbol[expr, symbol] explicitly names this symbol.
The internal format of expr should be f[s,...] where f and s should be
symbols. If expr=f[s] should have superscript format, the function
NewSuperscript[f, s] should be called before UseAsSymbol."

SuperLie`StopUseAsSymbol::usage =
 "StopUseAsSymbol[expr] cancels the treating of expr as a single symbol."


Begin["$`"] (* =============================== Private ========== *)

(* Preprocessing: generic operations *)


$Pre=.


preRule0=
 {WithoutPreSL[expr___]:>Sequence[expr],
  Times->GTimes$,
  Plus->GPlus$,
  Power->GPower$
 }


VectScalQ = (VectorQ[#]||ScalarQ[#])&

Vector[VTimes$,SVTimes$,VPlus$,VPower$]
Scalar[Times$,Plus$,Power$]

VectorQ[GPlus$[__?VectorQ]] ^:= True
ScalarQ[GPlus$[__?ScalarQ]] ^:= True

VectorQ[GTimes$[___?VectScalQ, _?VectorQ, ___?VectScalQ]] ^:= True
ScalarQ[GTimes$[__?ScalarQ]] ^:= True

VectorQ[GPower$[a_,_]] ^:= VectorQ[a]
ScalarQ[GPower$[a_,_]] ^:= ScalarQ[a]


Attributes[preVectorQ]^={HoldAll};
Attributes[preScalarQ]^={HoldAll};
Attributes[preVectScalQ]^={HoldAll};

preVectorQ[GPlus$[__?preVectorQ]] ^:= True
preScalarQ[GPlus$[__?preScalarQ]] ^:= True

preVectorQ[GTimes$[___?preVectScalQ, _?preVectorQ, ___?preVectScalQ]] ^:= True
preScalarQ[GTimes$[__?preScalarQ]] ^:= True

preVectorQ[GPower$[a_,_]] ^:= preVectorQ[a]
preScalarQ[GPower$[a_,_]] ^:= preScalarQ[a]

preScalarQ[x_Symbol] = ConstantQ[Unevaluated[x]]
preScalarQ[_Number]=True;

preVectorQ[x_Symbol] = VectorQ[Unevaluated[x]]
preVectorQ[x_Symbol[___]] = VectorQ[Unevaluated[x]]


preRule =
 {
  GTimes$[a__?preScalarQ] :> Times$[a],
  GTimes$[a__?preVectorQ] :> VTimes$[a],
  GTimes$[a__?preScalarQ,b__?preVectorQ] :> SVTimes$[Times$[a],VTimes$[b]],
  GTimes$[b__?preVectorQ,a__?preScalarQ] :> SVTimes$[Times$[a],VTimes$[b]],
  GTimes$[l___?preVectorQ,a__?preScalarQ,b__?preVectorQ,r___] :>
  	 GTimes$[l,SVTimes$[Times$[a],VTimes$[b]],r],
  GPlus$[a__?preVectorQ] :> VPlus$[a],
  GPlus$[a__?preScalarQ] :> Plus$[a],
  GPower$[a_?preVectorQ,b_?preScalarQ] :> VPower$[a,b],
  GPower$[a_?preScalarQ,b_?preScalarQ] :> Power$[a,b],
  Times$[a_] :> a,
  VTimes$[a_] :> a,
  GTimes$[a_] :> a,
  Plus$[a_] :> a,
  VPlus$[a_] :> a,
  GPlus$[a_] :> a
 }
 
preRule1 =
    {
	HoldPattern[Vect$[a_]] :> a,
	HoldPattern[Scal$[a_]] :> a
    }
    
preRule2 =
    {Plus$->Plus,
     VPlus$->VPlus,
     GPlus$->GPlus,
     Times$->Times,
     VTimes$->VTimes,
     SVTimes$->SVTimes,

     GTimes$->GTimes,
     Power$->Power,
     VPower$->VPower,
     GPower$->GPower
    }

PreSL[expr_] := ReleaseHold[Hold[expr]/.preRule0//.preRule//.preRule1/.preRule2]

PreSL[WithoutPreSL[expr_]] := expr


Attributes[PreSL] = {HoldAllComplete}

$Pre = PreSL

Vector[Vect$]
Scalar[Scal$]

(***** Transform the tensor and exterior power ****)

(* conversion from the old version *)
tp = CircleTimes
(* ep = Wedge *)
Tp = NonCommutativeMultiply

(* new power operation (for an existing times-type operation)
   Define the input/output format as "a ^symbol b" or "a" with
   superscript "symbol b" *)

(*
UniquePrivate[x_]:=
  Symbol[ToString[SequenceForm["$`",x,"$",$ModuleNumber++]]]
*)

NewPower[power_, symbol_, texsymbol_] :=
 With[{tmp=Unique[power]},
  With[{tmpname=SymbolName[tmp]},
   $`powerTmp[power] ^= tmp;
   $`powerSymbol[power] ^= symbol;
   GPower[b_,tmp[n_]] ^:= power[b,n];
   MakeExpression[RowBox[{symbol,a_}], form_] :=
      MakeExpression[RowBox[{tmpname, "[", a, "]"}], form ];
   Format[power[a_,n_],OutputForm] := 
     If[DivPowersQ[a,power],
       PrecedenceForm[Superscript[a,SequenceForm["(", symbol, n, ")"]], 190],
       PrecedenceForm[Superscript[a,SequenceForm[symbol, n]], 190]];
(*   Format[power[a_,n_],TeXForm] :=
     If[DivPowersQ[a,power],
       PrecedenceForm[Superscript[a,SequenceForm["(", texsymbol, n, ")"]], 190],
       PrecedenceForm[Superscript[a,SequenceForm[texsymbol, n]], 190]]; *)
   MakeBoxes[power[a_,b__],ft_] ^:= 
     SuperscriptBox[PrecedenceBox[a, 590, ft], 
       If[DivPowersQ[a,power],
         RowBox[{"(", symbol, PrecedenceBox[b,400,ft], ")"}],
	 RowBox[{symbol, PrecedenceBox[b,400,ft]}]]]
  ]]

RemovePower[power_] :=
  With[{tmp=$`powerTmp[power], symbol=$`powerSymbol[power]},
   tmp/: GPower[b_,tmp[n_]]=.;
   MakeExpression[RowBox[{symbol,a_}], form_]=.;
   Clear[power]
  ]


NewPower[tPower, "\[CircleTimes]", "\[CircleTimes]"];

NewPower[wPower, "\[Wedge]", "\[Wedge]"];

(*
MakeExpression[RowBox[{"\[Wedge]",a_}], form_] :=
  MakeExpression[RowBox[{"$`Wedgepw", "[", a, "]"}], form ];

GPower[b_,$`Diamondpw[n_]] ^:= DiamondPower[b,n];

MakeExpression[RowBox[{"\[Diamond]",a_}], form_] :=
  MakeExpression[RowBox[{"$`Diamondpw", "[", a, "]"}], form ];
*)

(*=== Define new superscript function (as SuperPlus) === *)

NewSuperscript[name_, symb_, tex_:None] :=
  ($`supSymbol[name] ^= symb;
   $`supTeX[name] ^= tex;
   MakeExpression[SuperscriptBox[base_,symb],form_]:=
	 MakeExpression[RowBox[{name,"[", base, "]"}],form];
   MakeBoxes[name[base_],form_] ^:=
	SuperscriptBox[MakeBoxes[base,form],symb];
   Format[name[base_],OutputForm] := base^symb;
   If[tex=!=None, Format[name[base_],TeXForm] := base^tex]
  )

$`supSymbol[Global`SuperStar] = "*"
$`supSymbol[Global`SuperPlus] = "+"
$`supSymbol[Global`SuperMinus] = "-"
$`supSymbol[Global`SuperDagger] = "\[Dagger]"

RemoveSuperscript[name_] :=
 With[{symb=$`supSymbol[name]},
    MakeExpression[SuperscriptBox[base_,symb],form_]=.;
    Clear[name]
 ]

(*=== Define new overscript function (as OverBar) === *)

NewOverscript[name_, symb_, tex_:None] :=
  ($`overSymbol[name] ^= symb;
   MakeExpression[OverscriptBox[base_,symb],form_]:=
	 MakeExpression[RowBox[{name,"[", base, "]"}],form];
   MakeBoxes[name[base_],form_] ^:=
	OverscriptBox[MakeBoxes[base,form],symb];
   Format[name[base_],OutputForm] := base^symb;
   If[tex=!=None, Format[name[base_],TeXForm] := base^tex]
  )

(*
$`overSymbol[Global`OverBar] = "_"
$`overSymbol[Global`OverTilde] = "~"
$`overSymbol[Global`OverHat] = "^"
$`overSymbol[Global`OverVector] = "\[RightVector]"
$`overSymbol[Global`OverDot,1] = "."
$`overSymbol[Global`OverDot,2] = ".."
*)

RemoveOverscript[name_] :=
 With[{symb=$`overSymbol[name]},
    MakeExpression[OverscriptBox[base_,symb],form_]=.;
    Clear[name]
 ]

(*=== Usage of sub- and overscripted expressions as symbols ===*)

UseAsSymbol[expr:f_[x_Symbol,___]] :=
  UseAsSymbol[expr, Unique[x]]

UseAsSymbol[f_[x_Symbol,parm___],alias_]:=
  ( x/: f[x,parm]=alias;
    Format[alias]= HoldForm[f[x,parm]];
(*    Format[alias,TeXForm]= HoldForm[f[x,parm]];*)
    Format[alias,StandardForm]= HoldForm[f[x,parm]];
    Format[alias,TraditionalForm]= HoldForm[f[x,parm]];
    If [ValueQ[$`supSymbol[f]],
      With[{sup=$`supSymbol[f], xtxt=ToString[x], tex=$`supTeX[name]},
	    MakeExpression[SubsuperscriptBox[xtxt,sub_,sup], fmt_] :=
	   (*   MakeExpression[RowBox[{alias,"[", sub, "]"}], fmt];	*)
	      MakeExpression[SubscriptBox[alias, sub], fmt];
       MakeBoxes[alias[sub__], fmt_] ^:=
	      With[{isub=InfixArgs[sub]},
            SubsuperscriptBox[xtxt,MakeBoxes[isub,fmt],sup]];
	    Format[alias[sub__],OutputForm] := Subscripted[alias[sub]];
	    If[tex=!=None,
	      Format[alias[sub__],TeXForm] :=
	        With[{isub=InfixArgs[sub]},
	          SubsuperscriptBox[xtxt,MakeBoxes[isub],tex]]]
    ]];
    alias
  )

StopUseAsSymbol[expr:f_[x_Symbol,parm___]] :=
  ( Clear[Evaluate[expr]];
    x/: expr=.;
    If [ValueQ[$`supSymbol[f]],
      With[{sup=$`supSymbol[f], xtxt=ToString[x]},
	MakeExpression[SubsuperscriptBox[xtxt,sub_,sup], fmt_]=.]]
  )



Attributes[StopUseAsSymbol] ^= {HoldFirst}

InfixArgs[expr_] := expr
InfixArgs[expr__] := Infix[{expr},","]


(* -------- Output and TeX formats ----------------- *)


NewProperty[Output, {Format}]
NewProperty[TeX, {Format}]
NewProperty[Standard, {Format}]
NewProperty[Traditional, {Format}]

(* + and * *)

Precedence[VPlus] ^=315
Precedence[VTimes] ^=405
Precedence[SVTimes] ^=399
Precedence[VPower] ^=595

SetProperties[VTimes, 
	{ Output->InfixFormat["*", Prec->405] (*,
	  TeX->InfixFormat["\[CenterDot]", Prec->148 ]*)
 } ]

SignedForm[SVTimes[Times[n_/;n<0,s_.], v_]] :=
		PrecedenceForm[Prefix[{SVTimes[(-n)*s, v]}, "- ", 144], 142]
SignedForm[v_] := PrecedenceForm[Prefix[HoldForm[PrecedenceForm[v, 650]], "+ "], 142]
SignedForm[v__] := SignedForm /@ Unevaluated[v]

Format[VPlus[first_, next__], OutputForm] :=
		 PrecedenceForm[Infix[{first, SignedForm[next]}, " ", 140], 140]
Format[VPower[a_,n_], OutputForm] :=
  If[DivPowersQ[a],
    PrecedenceForm[Superscript[a,SequenceForm["(",n,")"]], 190],
    PrecedenceForm[Superscript[a,n], 190]];

Format[expr_SVTimes, OutputForm] := PrecedenceForm[Infix[expr, " ",150], 150]
Format[SVTimes[-1,v_], OutputForm] := PrecedenceForm[Infix[{"-",v}, " ",150], 150]

(*Format[VPlus[first_, next__], TeXForm] :=
		PrecedenceForm[Infix[{first, SignedForm[next]}, " ", 140], 140]
Format[expr_SVTimes,TeXForm] := PrecedenceForm[Infix[expr, "\[ThinSpace]", 150], 150]
Format[SVTimes[-1,v_],TeXForm] := PrecedenceForm[Infix[{"-",v}, "\[ThinSpace]", 150], 150]
Format[VPower[a_,n_], TeXForm] :=
  If[DivPowersQ[a],
    PrecedenceForm[Superscript[a,SequenceForm["(",n,")"]], 190],
    PrecedenceForm[Superscript[a,n], 190]];
*)

MakeBoxes[VPlus[a_,b__],ft_] ^:= 
  RowBox[{MakeBoxes[a, ft], SignedBoxes[b,ft]}]
SignedBoxes[a_,b__,ft_] :=
  Sequence @@ (SignedBoxes[#,ft]& /@ {a,b})
SignedBoxes[SVTimes[Times[n_/;n<0,s_.], v_], ft_] := 
  With[{w=SVTimes[-n*s, v]},
    Unevaluated[Sequence["-", PrecedenceBox[w,318,ft]]]]
SignedBoxes[a_,ft_] := Sequence["+",PrecedenceBox[a,315,ft]]


MakeBoxes[e_VTimes, fmt_] ^:= 
  InfixBoxes[e, "\[ThinSpace]", 405, "1", fmt]

MakeBoxes[VPower[a_,b_],ft_] ^:=
  If[DivPowersQ[a],
    SuperscriptBox[PrecedenceBox[a, 590, ft], RowBox[{"(",MakeBoxes[b,ft],")"}]],
    SuperscriptBox[PrecedenceBox[a, 590, ft], MakeBoxes[b,ft]]];

MakeBoxes[SVTimes[a_,x_],ft_] ^:= 
  RowBox[{PrecedenceBox[a, 399, ft],
    "\[ThinSpace]",
     PrecedenceBox[x, 399, ft]}]

MakeBoxes[SVTimes[-1,x_],ft_] ^:= 
  RowBox[{"-", "\[ThinSpace]",
     PrecedenceBox[x, 399, ft]}]

(* tp, tPower *)

(*
SetProperties[CircleTimes,
	{ Output->InfixFormat["#", Prec->145],
	  TeX->InfixFormat["\[CircleTimes]", Prec->398]
 } ]

Format[tPower[a_,n_],OutputForm] :=
  PrecedenceForm[Superscript[a,SequenceForm["\[CircleTimes]", n]], 190]
Format[tPower[a_,n_],TeXForm] :=
  PrecedenceForm[Superscript[a,SequenceForm["\[CircleTimes]", n]], 190]
 Infix[{a, SequenceForm["^{*",n,"}"]}, "", 190]

MakeBoxes[tPower[a_,b__],ft_] ^:= 
  SuperscriptBox[PrecedenceBox[a, 590, ft],
	RowBox[{"\[CircleTimes]", PrecedenceBox[b,400,ft]}]]
*)

(* wedge *)

(*
SetProperties[Wedge,
	{ Output->InfixFormat["\[Wedge]", Prec->145],
	  TeX->InfixFormat["\[Wedge]", Prec->397]
 } ]

Format[ePower[a_,n_]] := Superscript[a, "\[Wedge]",n] (*, 190]*)
Format[ePower[a_,n_],TeXForm] :=
		Infix[{a, SequenceForm["^{{\wedge}", n, "}"]}, "", 190]
*)

(* Tp *)

Unprotect[NonCommutativeMultiply]

(*
SetProperties[NonCommutativeMultiply,
	{ Output->InfixFormat["\[Times]", Prec->150, Empty->"I"],
	  TeX->InfixFormat["\\cross ", Prec->150, Empty->"I"],
	  Standard->InfixFormat["\[Times]", Prec->397],
	  Traditional->InfixFormat["\[Times]", Prec->397]
 } ]
*)

(* Diamond: the product in the enveloping algebra *)


(* In Math 3.0  no Infix Precedence not supported *)

MakeBoxes[Infix[e_, h_, prec_,gr___], FormatType_]:= 
 MakeBoxes[Infix[e, h], FormatType]

(*
   Infix[ PrecedenceBox[#,prec,FormatType]& /@ e, h],
   FormatType]
*)
(*
MakeBoxes[Prefix[e_, h_, prec_], FormatType_]:= 
  MakeBoxes[PrecedenceForm[Prefix[e,h],prec],FormatType]
*)

InfixBoxes[expr_, sep_,prec_,empty_,fmt_]:=
	Switch[Length[Unevaluated[expr]],
	0, InterpretationBox[empty, expr],
	1, With[{f=Extract[Unevaluated[expr],{1},HoldForm]},
		With[{b=MakeBoxes[f,fmt][[1]]},InterpretationBox[b, expr]]],
	_, With[{boxes=List @@ InfixList[
              Function[x, PrecedenceBox[x,prec,fmt],{HoldFirst}]
	         /@ Hold @@ Unevaluated[expr],sep]},
	     RowBox[boxes]]]


Attributes[InfixBoxes]={HoldFirst}


PrecedenceBox[a_,p_,ft_] :=
    If[Precedence[Head[Unevaluated[a]]]>=p,
	 MakeBoxes[a,ft],
	 RowBox[{"(", MakeBoxes[a,ft], ")"}]]

Attributes[PrecedenceBox]={HoldFirst}

InfixList[e_,sep_]:=
	Module[{n=Length[e],res={First[e]}},
		Do[res={Sequence@@res,sep,e[[i]]},{i,2,n}];
		res]

Attributes[InfixList]={HoldFirst}

(*
Cell[BoxData[
    FormBox[
      RowBox[{"a", "+", "b"}], TraditionalForm]], "Output",
  CellLabel->"Out[56]//TraditionalForm="]
*)



End[]
