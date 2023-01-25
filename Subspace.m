(********************* SubSpace **************************)
BeginPackage[
  "SuperLie`Subspace`", {"SuperLie`", "SuperLie`Space`",  
    "SuperLie`Genvect`", "SuperLie`Domain`","SuperLie`Vsplit`", "SuperLie`Enum`"}]

SuperLie`Subspace`KerSpace::usage = 
 "KerSpace[sub, in, fn] calculates the subspace sub={v\[Element]in\
\[VerticalSeparator]fn(v)=0}. fn is a linear function or a list of linear \
functions."

SuperLie`Subspace`GradedKerSpace::usage = 
 "GradedKerSpace[sub, in, fn] calculates the subspace sub={v\[Element]in\
\[VerticalSeparator]fn(v)=0}. fn is a linear function or a list of linear \
functions. The oprions From->degree and To->degree restricts the \
calculations to the specified degrees (defaults 0 and ToGrade[in])."

Begin["$`"]

KerSpace[n_,in_,fn_,opts___] :=
  Module[ {c, img},
    img = GeneralSum[c,Basis[in]];
    img = GeneralZero[fn,img,c,#1[#2]&];
    img=GeneralBasis[img,c];
    VectorSpace[n, InSpace->in, PList->P /@ img, opts];
    Image[n]^=img;
    Image[n,in]^=img;
    DefMapping[Mapping/.{opts}, n, img];
    n::usage = SPrint["`` is a subspace in ``", n, in]
  ]


GradedKerSpace[n_,in_,fn_,opts___]:=
 Module[ {c, img, range, pos=1, plist, bas},
  With [{from = From/.{opts}/.From->0,
         to = To/.{opts}/.To->ToGrade[in],
         split = Split/.{opts}/.Split->P},
   VectorSpace[n, InSpace->in, Sequence@@ComplementKeys[{opts},{From,To,Split}]];
   Dim[n,d_/;d<from]^=0;
   PDim[n,d_/;d<from]^={0,0};
   Image[n]^={};
   PList[n]^={};
   RangeIndex[n,d_/;d<from]^=pos=1;
   For[range=from,range<=to,++range,
    DPrint[1, "Range=",range];
     bas = Basis[in,range];
     If[split=!=False,
       img = {};
       ForSplit[{SplitList[bas, _, split], m},
        DPrint[3, "Soving for ", m];
	img = {img, GeneralBasis[GeneralZero[fn,m,c,#1[#2]&],c]}];
       img = Flatten[img],
     (*else*)
       img = GeneralSum[c,bas];
       img = GeneralZero[fn,img,c,#1[#2]&];
       img = GeneralBasis[img,c]];
     n/: Image[n] = Join[Image[n],img];
     n/: Dim[n,range] = Length[img];
     plist = P /@ img;
     n/: PList[n] = Join[PList[n],plist];
     n/: PDim[n,range] = {Count[plist,0],Count[plist,1]};
     n/: RangeIndex[n,range] = pos;
     pos+=Length[img]];
   P[n[i_]] ^:= PList[n][[i]];
   Image[n,in]^=img;
   DefMapping[Mapping/.{opts}, n, img];
   EnumSet[n,{from,to,1}-> {d_:> Array[n,Dim[n,d],RangeIndex[n,d]]}];
   n::usage = SPrint["`` is a subspace in ``", n, in]
  ]]
 
DPrint[1, "SuperLie`Subspace` loaded"]

End[]
EndPackage[]
