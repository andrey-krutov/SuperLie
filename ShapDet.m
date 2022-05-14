BeginPackage["SuperLie`ShapDet`", {"SuperLie`", "SuperLie`Domain`",
    "SuperLie`Enum`", "SuperLie`Space`", "SuperLie`Submod`", 
    "SuperLie`Envsort`", "SuperLie`Genvect`", "SuperLie`Generate`", 
    "SuperLie`Vsplit`", "SuperLie`Subalg`", "SuperLie`Symalg`", 
    "SuperLie`Irrmod`"}]

(*
This package defines functions for calculation of Shapovalov Determinants.
*)

sdDefAlg::usage=
 "sdDefAlg[g,{marks}] declares the algebra those Shapovalov determinant are computed.
The argument {marks} gives the list of replacement rules {h1->m1,...} that maps
the elements of Cartan subalgebra to the corresponding weight marks of the vacuum vector.
Options:
Order->fn sets the ordering function that define the order of the terms in U(g).
Split->fn defines the function used to split the U(g) in sum of subspaces ortogonal
with respect to the invariant bilinear form on U(g). By default a is splitted by weight and parity."

sd$Order::usage=
 "The value of sd$Order is a function used to order terms in enveloping product.
  sd$Order[x,y] should give True if the the pair (x,y) is in the order
  desired for terms of the enveloping product, and False otherwise.
  The default value of sd$Order is sdOrder."

sdOrder::usage=
 "The function sdOrder is used by default to order terms in enveloping product.
  sdOrder[x,y] gives True if either Grade[x]<Grade[y] or the grades are equals
  and the terms are either in canonical order (for grade>=0) or reversed
  canonical order (for grade<0). See also sd$Order."

sdVacuumAnnulatorQ::usage=
 "sdVacuumAnnulatorQ[up[...]] gives True if degrees of terms in up[...] are
  such that this element always annulate the vacuum vector in Verma module"

sdInvolution::usage =
 "sdInvolution[x] implements the involution on U[g]. It should be defined by the
  user on the basis of algebra g"

sdShapForm::usage =
 "sdShapForm[x,y] gives the value of <i(x)m0,i(y)m0> where x,y are elements of U(g+),
i is the involution, m0 is the vacuum vector and <,> is the invariant form.
The weights, grades, and parities of x and y should be equal."

sdShapFormInv::usage =
 "sdShapFormInv[x,y] gives the value of <i(x)m0, y m0> where x,y are elements of U(g+) and U(g-),
i is the involution, m0 is the vacuum vector and <,> is the invariant form.
The weights and grades of x and y should be oppesite, the parities should be equal."


sd$hRepl::usage =
  "sd$hRepl is bound to the list of replacement rules that maps the elements
of the Cartan subalgebra to the corresponding weight marks of the vacuum vector."

sdFormTo::usage =
  "sdFormTo[file] instruct the program to write the matrix elements of the invariant
form to the given file. The option Clear->True instructs program to clear the file."

sdCalcForm::usage =
 "sdCalcForm[r] calculates and save to file (defuned by sdFormTo) the matrix elements of the
invariant form up to the elements of grade r. sdCalcForm[r,{n,i,j}] starts calculations with
the matrix element (i,j) of the n-th component of the splitted U(g+)."

sd$Calc::usage =
 "When calculating matrix element (i,j) of the n-th component of the splitted U(g+), sd$Calc is bound to {n,i,j}."

(* ======  Private ======== *)
Begin["sd`"]

sdOrder[x_, y_] :=
  With[{rx = Grade[x], ry = Grade[y]}, 
    Which[rx < ry, True, rx > ry, False, rx >= 0, OrderedQ[{x, y}], rx < 0, 
      OrderedQ[{y, x}], True, True]]

sdVacuumAnnulatorQ[v_up] :=
  Module[{i,r=0},
    For[i=Length[v],i>=0,i--,
      r += Grade[v[[i]]];
      If[r>0, Return[True]]];
    False]

SetProperties[sdInvolution, {Vector, Vector -> _, Linear}];
sdInvolution[v_up] := Reverse[sdInvolution /@ v];



sdDefWeights::usage =
  "sdDefWeights[h1->w1,...] introduce notations for weight marks of vacuum vector"

sdDefWeights[rules___]:=
  (sd$hRepl = {rules};
   Scalar@@Union[(Tag/@Last/@{rules})/. v_HoldPattern :> v[[1]]];
  )

sd$hRepl={};

PreShap[g1_, g2_] := g1\[CenterDot]Involution[g2]

sdShapForm[g1_, g2_] := 
  CenterDot[g1,sdInvolution[g2]] /. sd$hRepl /. {up -> Times, 
        SVTimes -> Times, VPlus -> Plus, VPower -> Power}

sdShapFormInv[g1_,g2_] :=
 CenterDot[g1,g2] /. sd$hRepl /. {up -> Times, SVTimes -> Times, 
        VPlus -> Plus, VPower -> Power}

Options[sdDefAlg] ^={Order->sdOrder, Split->({Grade[#], Weight[#], P[#]}&)}

sdDefAlg[g_, marks_, opts___Rule]:=
  (sd$Alg = g;
   sd$hRepl = marks;
   sd$Order = Order/.{opts}/.Options[sdDefAlg];
   sd$Split = Split/.{opts}/.Options[sdDefAlg];
   Clear[sdBasis]; sdBasis[0]={};
   sdBasis[k_] := sdBasis[k] = Join[sdBasis[k-1],Sort[Basis[sd$Alg,k],sd$Order]];
   Scalar@@Union[(Tag/@Last/@marks)/. v_HoldPattern :> v[[1]]];
   EnvelopingSymbol[up, CenterDot, Bracket[g], sd$Order, sdVacuumAnnulatorQ]
)



sdUBasis[k_] :=
   SplitList[FilterBasis[k, sdBasis[k], up], _, sd$Split]


sdFormTo[False, opts___]:= (sd$FormFile=False);

sdFormTo[file_String, opts___]:=
 (sd$FormTo = file;
  If[(Clear/.{opts})===True, Close[OpenWrite[file]]];
 )

sdSave[arg__] :=
  If[sd$FormTo=!=False,
    With [{res = OpenAppend[sd$FormTo]},
      Write[res, arg];
      Close[res];
    ]
  ]

sdCalcForm[k_, cp_:{1,1,1}] :=
  Module[{vs, l, i0, j0, n0, i, j, n, vt, lv},
   vs = sdUBasis[k];
   l = Length[vs];
   {n0,i0,j0} = cp;
   For[n = n0, n <= l, ++n,
     vt = vs[[n,2]];
     lv = Length[vt];
     sdSave["\n"//OutputForm];
     sdSave[StringForm["n = ``, component = ``,  dim = ``",
		 n, vs[[n,1]], lv ]//OutputForm,
            "\n"//OutputForm];
     DPrint[1, StringForm["component = ``,  dim = ``", vs[[n,1]], lv ]];
     For [j=j0, j<=lv, ++j,
       vr = sdInvolution[ vt[[j]] ];
       For [i=i0, i<=lv, ++i,
         sd$Calc = {n,i,j};
         sdSave[
            If[i==j==1, "{", " "]//OutputForm,
	    If[i==1, "{", " "]//OutputForm,
	    Expand[sdShapFormInv[vt[[i]],vr]],
	    If[i==lv, If[i==j==lv, "}}", "},"], ","]//OutputForm
         ]
       ];
       i0 = 1
     ];
     j0 = 1
   ];
  ]

sdCalcForm[k_, cp_Integer] := sdCalcForm[k,{cp,1,1}]

shWriteDet[file_,title_, mat_]:=
 Module[{out, str},
  out = OpenAppend[file, FormatType->OutputForm];
  str = StringReplace[tit, {"{"->"$(", "}"->")$"}];
  str = StringDrop[ str, StringPosition[str, "Weight", 1][[1,1]]-1 ];
  Write[out, str ];
  Write[out, "$$"];
  det = Factor[Det[mat]];
  Print[det];
  Write[out, TeXForm[det]];
  Write[out, "$$" ];
  Write[out, "" ];
  Close[out];
 ]

End[]
EndPackage[]
 
