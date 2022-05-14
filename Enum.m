(* ------- Enum.m -------------------------------------------------- #)
>
>	The package for enumerating the sets
>
>     The enumeration of the set have the format 
>	Enum[set,i] = {deg:>list, ...}
>  where
>   set   is the symbol representing the set,
>   i     is the number of the component, 1<=i<=Enum[set], 
>   deg   is an integer or a pattern representing an integer,
>   list  is the list of elements of this degree (or the function
>	  generating the list)
>
>     The bounds of the degree are defined as EnumRange[set,i] =
>   {start, end, step}. The end can be Infinity (or -Infinity).
>
(# ----------------------------------------------------------------- *)

BeginPackage["SuperLie`Enum`"]

EnumFor::usage =
 "EnumFor[var, set, options..., body] executes body for any var from set.
Options are: Range->range or Range->{from,to,[step]} restricts the range
of elements; From->elt, FromNext->elt, To->elt, Until->elt give the first
and the last element."

EnumTable::usage =
 "EnumTable[expr, {var,set,options...}] generates a list of the values of
expr when var runs over all elements of the enumerated set. The options
(see EnumFor) restricts the range of elements. The EnumTable[expr, iter ...]
with several iterators gives a nested list, the first iterator is outermost."

EnumList::usage =
 "EnumList[set,options...] generates the list of elements of the enumerated
set. The options (see EnumFor) restricts the range of elements."

EnumPoint::usage =
 "EnumPoint[var, set, elt, options...] finds the location of the elt in
the set and assign the var to point the result. The options are the same
as for EnumFor."

From FromNext To Until

EnumSet::usage =
 "EnumSet[set, range1->comp1, ...] builds new enumerated set from given
components. The result is attached to the symbol in first argument.
The arguments must have format {start,end,step}->{deg:>{list}, ... }."

EnumAddTo::usage =
 "EnumAddTo[set, range1->comp1, ...] adds the components to the enumerated set."

EnumJoin::usage =
 "EnumJoin[new, set1, ...]  builds new enumerated set joining the enumerated
sets set1, set2, ..., setn. EnumJoin[new, old] builds the duplicate of old."

Enum::usage =
 "Enum[set, i] is the component of the enumeration of the set. Enum[set] is
the number of the components in the enumeration of the set."
 
EnumRange::usage =
 "EnumRange[set, no] = {stars, end, step} is the range iterator of the component
 set[no] of the enumerated set."

TestRange::usage =
 "TestRange[val, range] tests whether val is in the given range. The range must
 be {end}, {start,end} or {start, end, step}. Returns True, False, Greater or
 Less." 

(* ===================== *) Begin["enm`"] (* ============================ *)

Attributes[EnumStart] = {HoldFirst}
Attributes[EnumPos] = {HoldFirst}

EnumStart[elt_, set_] := 
  Module[{range, deg, list, len},
    Do [
      range = EnumRange[set,no];
      deg = range[[1]];
      If [! TestRange[deg, range], Continue[] ];
      list = deg /. Enum[set,no];
      len = Length[list];
      EnumPos[elt] ^= {no, deg, 0, len};
      Break[],
     { no, 1, Enum[set] }
    ]
  ]

EnumStart[elt_, set_, deg_] :=
  Module[{range, list, len},
    Do [
      range = EnumRange[set,no];
      If [! TestRange[deg, range], Continue[] ];
      list = deg /. Enum[set,no];
      len = Length[list];
      EnumPos[elt] ^= {no, deg, 0, len};
      Break[],
     { no, 1, Enum[set] }
    ]
  ]
  

TestRange[x_, {strt_, end_, step_}] :=
 If [step>0,
   Which[
     x < strt, Less,
     x > end,  Greater,
     True, Mod[(x-strt), step]===0
   ],  
  (*else*)
   Which[
     x > strt, Less,
     x < end,  Greater,
     True, Mod[(strt-x), -step]===0
   ]
 ]  
  
TestRange[x_, {strt_, end_, 1}] :=
  Which[ x < strt, Less, x > end,  Greater, True, True ]

TestRange[x_, {strt_, end_}] :=
  Which[ x < strt, Less, x > end,  Greater, True, True ]

TestRange[x_, {end_}] :=
  Which[ x < 1, Less, x > end,  Greater, True, True ]

TestRange[x_, {strt_, end_, -1}] :=
  Which[ x > strt, Less, x < end,  Greater, True, True ]

Attributes[EnumNext] = {HoldFirst}

EnumNext[elt_, set_] :=
  Module[{range, no, deg, ind, list, len},
    {no, deg, ind, len} = EnumPos[elt];
    If [ind < len,
       EnumPos[elt] ^= {no, deg, ++ind, len};
       Return [ (deg /. Enum[set,no])[[ind]] ],
    (*else*)
       range = EnumRange[set,no];
       ind = 1;
       While [ True,
         Switch [TestRange[ deg += range[[3]], range ],
	    False, 
		Continue[],
            Greater,
		If [(++no) > Enum[set], Return[EnumEnd] ];
		range = EnumRange[set,no];
		deg = range[[1]] - range[[3]];
		Continue[],
	    Less,
		deg = range[[1]] - range[[3]];
		Continue[],
	    True,
		list = deg /. Enum[set,no];
		len = Length[list];
		If [len==0, Continue[] ];
		EnumPos[elt] ^= {no, deg, 1, len};
		Return[ list[[1]] ]
          ]
       ]
     ]  
  ]

EnumNext[elt_, set_, todeg_, step_:1] :=
  Module[{range, no, deg, ind, list, len, i},
    {no, deg, ind, len} = EnumPos[elt];
    If [ind < len,
       EnumPos[elt] ^= {no, deg, ++ind, len};
       Return [ (deg /. Enum[set,no])[[ind]] ]
    ];
    While[True,
         For [ i=no+1, i<=Enum[set], ++i,
           range = EnumRange[set,i];
           If [ TestRange[deg, range]=!=True, Continue[] ];
           list = deg /. Enum[set,i];
           len = Length[list];
           If [len==0, Continue[] ];
	   EnumPos[elt] ^= {i, deg, 1, len};
	   Return[ list[[1]] ]
         ];
         deg += step;
         If [step>0 && deg>todeg || step<0 && deg<todeg, Break[] ];
         no = 0
    ];
    Return[EnumEnd] 
  ];

 
EnumSet[set_, comp___] :=
( Enum[set] ^= 0;
  EnumAddTo[set, comp]
)

 
EnumAddTo[set_, comp___] :=
  With [{no = Enum[set]},
    MapIndexed [ ( set/: EnumRange[set, First[#2]+no ] = First[#1];
		   set/: Enum[set, First[#2]+no ] = Last[#1] )&,
	        {comp}
    ];
    Enum[set] ^= no + Length[{comp}]
  ]


EnumJoin[new_, old___] :=
  Module[{no=0, set},
    Do [ set = {old}[[i]];
           Do [ new/: EnumRange[new, no+j] = EnumRange[set, j];
                new/: Enum[new,no+j] = Enum[set,j],
              {j, Enum[set] }
           ];
         no += Enum[set],
       {i, Length[{old}]}
    ];
    Enum[new] ^= no
  ]
  
EnumRange[set_] :=
  Module[{rmin=Infinity, rmax=-Infinity, rng},
    Do [rng = EnumRange[set,i];
      If [rng[[3]]>=0, rmin = Min[rmin, rng[[1]]]; rmax = Max[rmax, rng[[2]]],
	  (*else*) rmin = Min[rmin, rng[[2]]]; rmax = Max[rmax, rng[[1]]]
      ],
      {i, Enum[set]}
    ];
    {rmin, rmax}
  ]

Attributes[EnumFor] = {HoldAll}

EnumFor[var_Symbol, set_, opts___, body_] :=
 Module[{from, fromnext, to, upto, range, rangeto, optlist, EnumTest},
   optlist = Unevaluated[{opts}] /.
       Literal[(op:(From|FromNext))->el_]:>(op->EnumPos[el]);
   {from, fromnext, to, upto, range} =
	{From, FromNext, To, Until, Range} /. optlist;
   EnumTest := Which[
     upto=!=Until, (#=!=upto)&,
     to=!=To,  (If [#===to, EnumTest = (False&)]; True)&,
     True, True&
   ];
   If [range===Range,
     rangeto = Sequence[];
     Which[
       fromnext=!=FromNext,  EnumPos[var] ^= fromnext,
       from=!=From,  EnumPos[var] ^=
		MapAt[(# - 1)&, from, 3],
(*		MapAt[(# - EnumRange[set,from[[1]]][[3]])&, from, 3], *)
       True, EnumStart[var, set]
     ],
   (*else*)
     If[Head[range]=!=List, range={range,range,1}];
     EnumStart[var, set, range[[1]]];
     rangeto = Sequence @@ Rest[range];
     Which[
       fromnext=!=FromNext, 
          Switch [ TestRange[ fromnext[[2]], range],
             True|False,  EnumPos[var] ^= fromnext,
             Greater,     EnumTest ^= False&
          ],
       from=!=From,
          Switch[ TestRange[ from[[2]], range],
             True|False,  EnumPos[var] ^=
		MapAt[(# - 1)&, from, 3],
(*		MapAt[(# - EnumRange[set,from[[1]]][[3]])&, from, 3], *)
             Greater,     EnumTest = False&
          ]
     ]
   ];
   While[(var=EnumNext[var, set, rangeto])=!=EnumEnd && EnumTest[var], body]
 ]

EnumFor[var_, ___] := Null/; (Message[EnumFor::sym, var, 1]; False)


Attributes[EnumPoint] = {HoldAll}

EnumPoint[var_Symbol, set_, elt_, opts___] :=
  Module[{ret=$Failed},
    EnumFor[var, set, opts, If[var===elt, ret=Null; Break[]] ]; 
    var =.;
    ret
  ] 

EnumPoint[var_, ___] := Null/; (Message[EnumPoint::sym, var, 1]; False)


Attributes[EnumTable] = {HoldAll};

EnumTable[expr_, {var_,set_,opts___Rule}] :=
  Module[{res={}, hd},
    EnumFor[var, set, opts, res = {res, hd[expr]}];
    First /@ Flatten[res]]

EnumTable[expr_, iters__, iter_] :=
  EnumTable[EnumTable[expr,iter], iters]

EnumList[set_,opts___Rule] :=
  Module[{res={}, var, hd},
    EnumFor[var, set, opts, res = {res, hd[var]}];
    First /@ Flatten[res]]

 
End[]
EndPackage[]
