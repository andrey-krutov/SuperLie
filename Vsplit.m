(* ::Package:: *)

(******************* Split Expressions ***************************)
(* Splits the expression "expr" (list or sum) in the parts contained terms 
 * matching "ptrn" with different value of function func[term].
 * The result {func[term]->part, ... } is sorted.
 * The term with func[term]==SkipVal is omitted.
 * If "expr" is not a sum or a list the result is {func[term]->expr} 
 *******)

BeginPackage["SuperLie`Vsplit`", {"SuperLie`", "SuperLie`Domain`"}]

(* ------------- Split expressions --------------------- *)

SplitSum::usage =
 "SplitSum[expr, ptrn] transform the expression c1*v1 + c2*v2 + ... with
v1, v2, .. matching pattern \"ptrn\", gathering terms with equals \"v\".
The result is the list { vi1->sc1, vi2->sc2, ... }, there 
where {vi1,vi2,..} is a sorted list of \"vi\" in expression and 
\"scj\" is the sum of coefficients of \"vij\".\n
  SplitSum[expr, ptrn, func] transforms the same expression into
a list { f1->se1, f2->se2, .. }, 
where {f1,f2,..} is a sorted list of different values func[vi] and 
\"sej\".. is the sum of the members of \"expr\" giving value \"fj\" of
function \"func\" (not including members with func[vi]==SkipVal)."

SplitList::usage =
 "SplitList[expr, ptrn] transform the expression {c1*v1, c2*v2, ...} with
v1, v2, .. matching pattern \"ptrn\", gathering terms with equals \"v\".
The result is the list { vi1->lc1, vi2->lc2, ... }, there 
where {vi1,vi2,..} is a sorted list of \"vi\" in expression and 
\"lcj\" is the list of coefficients of \"vij\".\n
  SplitList[expr, ptrn, func] transforms the same expression into
a list { f1->le1, f2->le2, .. }, 
where {f1,f2,..} is a sorted list of different values func[vi] and 
\"lej\".. is the list of the members of \"expr\" giving value \"fj\" of
function \"func\" (not including members with func[vi]==SkipVal)."

ForSplit::usage =
 "ForSplit[{expr, memb, cnt}, body] or ForSplit[{expr, sel->memb, cnt}, body]
evaluates the body for each term of the splitted sum or list expr. The
variables sel and memb are assigned to the current values of the selector
and the member of the expr, the optional cnt is the loop counter.
The Break[], Continue[] and Return[value] can be used in the body." 

MergeSplit::usage =
 "MergeSplit[fn, expr, expr, ...] merges terms of splitted expression."

AddSplit::usage =
 "AddSplit[expr, expr, ...] adds terms of splitted sum."

JoinSplit::usage =
 "JoinSplit[expr, expr, ...] joins terms of splitted list."

ApplySplit::usage =
 "ApplySplit[func, expr, args...] applies function \"func\" to terms of splitted
sum or list."

MapSplit::usage =
 "MapSplit[func, expr] applies function \"func\" to member of lists -
terms of splitted list."

PartSplit::usage =
 "PartSplit[expr, sel] returns the part of splitted expression with
given selector."

SkipVal::usage =
 "\"SkipVal\" is the value of selection function for \"SplitSum\" and
\"SplitList\". If func[member]==SkipVal, \"member\" will be omitted."

Begin["$`"]

Split::nomatch = "No part of \"``\" matched \"``\"."

SplitVal[ptrn_,func_] :=
  With[{ val=func[ First[ SplitPtrn[ptrn][#] ] ] },
    If [ val===SkipVal, Unevaluated[Sequence[]], (*{val, #}*) val-># ]
  ]&


SplitSum[expr:_VPlus|_List, ptrn_, valf_] := 
     AddSplit[ SplitVal[ptrn, valf] /@ ReplacePart[expr,List,0] ]

SplitSum[expr_(*not List,VPlus*), ptrn_, valf_] := 
	{SplitVal[ptrn, valf][expr]}

SplitSum[expr_VPlus|_List, ptrn_] :=
	AddSplit[ SplitPtrn[ptrn] /@ ReplacePart[expr,List,0] ]

SplitSum[expr_(*not List,VPlus*), ptrn_] :=
	{ SplitPtrn[ptrn] [expr] }

SplitList[expr:_List|_VPlus, ptrn_, valf_] := 
     MergeSplit[List, SplitVal[ptrn, valf] /@ ReplacePart[expr,List,0] ]

SplitList[expr_(*not List,VPlus*), ptrn_, valf_] := 
	{MapAt[List, SplitVal[ptrn, valf][expr], 2]}

SplitList[expr_(*not List,VPlus*), ptrn_] := 
	{MapAt[List, SplitPtrn[ptrn][expr], 2]}

SplitList[expr_List|_VPlus, ptrn_] :=
	MergeSplit[List, SplitPtrn[ptrn] /@ ReplacePart[expr,List,0] ]


Attributes[ForSplit] = {HoldRest};

ForSplit[{expr_, sel_Symbol->memb_Symbol, i_Symbol:fs$ind}, body_] :=
  Do [ With[{sel=expr[[i,1]], memb=expr[[i,2]]}, body], {i, Length[expr]}]

ForSplit[{expr_, memb_Symbol, i_Symbol:fs$ind}, body_] :=
  Do [ With[{memb=expr[[i,2]]}, body], {i, Length[expr]}]

(*
AddSplit[expr___] :=
  Module [ {jexpr, val, coef, i0, w, res={} },
    jexpr = Join[expr] /. Rule->List;
    If[jexpr==={}, Return[{}] ];
    {val, coef} = Transpose[ Sort[ jexpr, OrderedQ[{First[#1],First[#2]}]& ] ];
    w = val[[1]];
    i0 = 1;
    Do [ If [val[[i]]=!=w,
		res = { res,  w->Take[coef, {i0,i-1}] };
		i0 = i;
		w = val[[i]]
	 ],
	{ i, Length[jexpr] }
    ];
    ApplySplit[ ReplacePart[#,VPlus,0]&,
			Flatten[{ res, w->Drop[coef, i0-1] }] ]
  ]
*)

MergeSplit[fn_, expr___] :=
  Merge[expr,
    Sort->(OrderedQ[{First[#1],First[#2]}]&),
    SameTest->(First[#1]===First[#2]&),
    Merge->((#[[1]]->fn@@Last/@{##})&)]

JoinSplit[expr___] := MergeSplit[Join, expr]

AddSplit[expr___] := MergeSplit[VPlus, expr]


(*
JoinSplit[expr___] :=
  Module [ {jexpr, val, coef, i0, w, res={} },
    jexpr = Join[expr] /. Rule->List;
    If[jexpr==={}, Return[{}] ];
    {val, coef} = Transpose[ Sort[ jexpr, OrderedQ[{First[#1],First[#2]}]& ] ];
    w = val[[1]];
    i0 = 1;
    Do [ If [val[[i]]=!=w,
		res = { res, w->Take[coef, {i0,i-1}] };
		i0 = i;
		w = val[[i]]
	 ],
	{ i, Length[jexpr] }
    ];
    Flatten[{ res, w->Drop[coef, i0-1] }]
  ]
*)

ApplySplit[func_, expr_] :=
  If [$DPrint>=3,
    (Print["Applying ", func, " to ", #[[1]]]; #[[1]]->func[#[[2]]])& /@ expr,
  (*else*)
    MapAt[func, #, 2]& /@ expr ]

ApplySplit[func_, expr_, args__] :=
  If [$DPrint>=3,
    (Print["Applying ", func, " to ", #[[1]]]; #[[1]]->func[#[[2]],args])& /@ expr,
  (*else*)
    MapAt[func[#,args]&, #, 2]& /@ expr ]

MapSplit[func_, expr_] :=
  If [$DPrint>=3,
    (Print["Mapping ", func, " to ", #[[1]]]; #[[1]]->(func/@#[[2]]))& /@ expr,
  (*else*)
     MapAt[func/@#&, #, 2]& /@ expr]


PartSplit[expr_, sel_, miss_:0] := With[{f=Cases[expr,_[sel,_]]},If[f==={},miss,f[[1,2]]]]

End[]
EndPackage[]
