(* ::Package:: *)

(*r0=7.0;
lminret=2;
lmaxret=10;
gridFile="h1Lorenz/input/radial_grid_r"<>ToString[r0(*N[r0]*)]<>".h5";
r0S[r0_]:=ToString[NumberForm[N[r0],{\[Infinity],1}]];
dataDir=FileNameJoin[{"data","h1","r0_"<>r0S[r0],"EvenStatic","h1ret"}];*)


Print["Computing even static modes:
r0="<>ToString[r0]<>"
lmin="<>ToString[lminret]<>"
lmax="<>ToString[lmaxret]<>"
grid="<>gridFile<>"
dataDir="<>dataDir];


If[!NumericQ[r0],Print["Numeric value for r0 not provided"]; Abort[];];
If[!(IntegerQ[lminret]&&EvenQ[lminret]),Print["Invalid value for lminret. Must be an even integer."]; Abort[];];
If[!(IntegerQ[lmaxret]&&EvenQ[lmaxret]),Print["Invalid value for lmaxret. Must be an even integer."]; Abort[];];
If[!FileExistsQ[gridFile],Print["Input grid file does not exist."]; Abort[];];
If[Sort[Import[gridFile]]!={"/ImportantIndexes","/r"},Print["Input grid file is not in expected format."]; Abort[];];
If[!DirectoryQ[dataDir], CreateDirectory[dataDir,CreateIntermediateDirectories->True]];


(* ::Section::Closed:: *)
(*M2af solutions*)


rules[r_]:={1/2 Log[r/M]-1/2 Log[-2+r/M]->-(1/2) Log[1-(2 M)/r]};


\[Psi]0H[l_,r_]:=r/M LegendreP[l,r/M-1];


\[Psi]1H[l_,r_]:=Module[{z=(2M)/r,s=1},z^(-l-1) Hypergeometric2F1[-l-s,-l+s,-2 l,z]];


\[Psi]2H[l_,r_]:=Module[{\[Lambda]=1/2 (l-1)(l+2)},-(4\[Lambda]^2 (1+\[Lambda])^2 r (-3 M+(3+\[Lambda]) r) LegendreP[l,r/M-1])/(M (3 M+\[Lambda] r))-(4\[Lambda]^2 (3+5 \[Lambda]+2\[Lambda]^2) (2 M-r) r^2 \!\(\*SuperscriptBox[\(LegendreP\), 
TagBox[
RowBox[{"(", 
RowBox[{"0", ",", "1"}], ")"}],
Derivative],
MultilineFunction->None]\)[l,r/M-1])/(M^2 (3 M+\[Lambda] r))
];


\[Psi]0\[Infinity][l_,r_]:=r/M LegendreQ[l,0,3,r/M-1]/.rules[r];


\[Psi]1\[Infinity][l_,r_]:=Module[{z=(2M)/r,s=1},z^l Hypergeometric2F1[1+l-s,1+l+s,2+2 l,z]];


\[Psi]2\[Infinity][l_,r_]:= Module[{\[Lambda]=1/2 (l-1)(l+2)},-(4\[Lambda]^2 (1+\[Lambda])^2 r (-3 M+(3+\[Lambda]) r) LegendreQ[l,0,3,-1+r/M])/(M (3 M+\[Lambda] r))-(4\[Lambda]^2 (3+5 \[Lambda]+2\[Lambda]^2) (2 M-r) r^2 Derivative[0,0,0,1][LegendreQ][l,0,3,r/M-1])/(M^2 (3 M+\[Lambda] r))/.rules[r]
];


M2afEqnH[l_,r_]:=Evaluate[Module[{R},With[{s=0,\[Lambda]=1/2 (l-1)(l+2)},Collect[r^2 (1-2M/r) M2af''[r]+2M M2af'[r]-(l(l+1)+(1-s^2) (2M)/r)M2af[r]-1/(l(l+1)) r^4 (1-2M/r)D[(C[1]\[Psi]0H[l,r])/r,r]+(r^3 (1-2M/r)((6+5\[Lambda])M+\[Lambda](1+\[Lambda])r))/((1+\[Lambda])(3M+\[Lambda] r)) D[C[2]\[Psi]2H[l,r],r]+(\[Lambda] r^2 (1-2M/r)(3M^2+6(1+\[Lambda])M r+\[Lambda](1+\[Lambda])r^2))/((1+\[Lambda])(3M+\[Lambda] r)^2) C[2]\[Psi]2H[l,r]/.M2af->Function[{R},R^2 (1-2M/R) a[R]+R M Log[(2M)/R]LegendreP[l,R/M-1] (C[1]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[2])/((-1+2 l) (1+2 l) (3+2 l)) ],{a[r],a'[r],a''[r]},Simplify]]]];


M2afEqn\[Infinity][l_,r_]:=Evaluate[Module[{R},With[{s=0,\[Lambda]=1/2 (l-1)(l+2)},Collect[r^2 (1-2M/r) M2af''[r]+2M M2af'[r]-(l(l+1)+(1-s^2) (2M)/r)M2af[r]-1/(l(l+1)) r^4 (1-2M/r)D[(C[4]\[Psi]0\[Infinity][l,r])/r,r]+(r^3 (1-2M/r)((6+5\[Lambda])M+\[Lambda](1+\[Lambda])r))/((1+\[Lambda])(3M+\[Lambda] r)) D[C[5]\[Psi]2\[Infinity][l,r],r]+(\[Lambda] r^2 (1-2M/r)(3M^2+6(1+\[Lambda])M r+\[Lambda](1+\[Lambda])r^2))/((1+\[Lambda])(3M+\[Lambda] r)^2) C[5]\[Psi]2\[Infinity][l,r]/.M2af->Function[{R},R M PolyLog[2,(2 M)/R]LegendreP[l,R/M-1] (C[4]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[5])/( (-1+2 l) (1+2 l) (3+2 l))-R M Log[(2M)/R]LegendreQ[l,0,3,R/M-1] (C[4]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[5])/( (-1+2 l) (1+2 l) (3+2 l))+a[R]Log[1-2M/R]+b[R]/.rules[r]],{a[r],a'[r],a''[r],b[r],b'[r],b''[r]},Simplify]]]];


ClearAll[a1];
a1[l_Integer,r_]:=a1[l,r]=Module[{cList,cSol,R,c},cList=CoefficientList[Collect[M2afEqnH[l,r]/.{a[R_]:>Sum[c[n] R^n,{n,0,l+1}],a'[R_]:>D[Sum[c[n] R^n,{n,0,l+1}],R],a''[R_]:>D[Sum[c[n] R^n,{n,0,l+1}],{R,2}]},r],r];
If[First[cList]!=0,Print["Error: first term not 0"];Abort[]];
cSol=Solve[cList[[2;;l+3]]==0,Table[c[n],{n,0,l+1}]][[1]];
If[(Last[cList]/.cSol)!=0,Print["Error: solution not found"];Abort[]];
Collect[Sum[c[n] r^n,{n,0,l+1}]/.cSol,{C[1],C[2]}]]


ClearAll[d1rule];
d1rule[c_,d_,l_Integer,r_]:=d1rule[l,r]=d[1]->-SeriesCoefficient[r M PolyLog[2,(2 M)/r]LegendreP[l,r/M-1] (C[4]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[5])/( (-1+2 l) (1+2 l) (3+2 l))+Sum[c[n] r^n,{n,2,l+3}]Log[1-2M/r],{r,\[Infinity],-1}];


ClearAll[a1\[Infinity]];
a1\[Infinity][l_Integer,r_]:=a1\[Infinity][l,r]=Module[{cList,cSol,R,c,d},cList=Flatten[CoefficientList[CoefficientList[Expand[M2afEqn\[Infinity][l,r]/.rules[r]/.{a[R_]:>Sum[c[n] R^n,{n,2,l+3}],a'[R_]:>D[Sum[c[n] R^n,{n,2,l+3}],R],a''[R_]:>D[Sum[c[n] R^n,{n,2,l+3}],{R,2}],b[R_]:>Sum[d[n] R^n,{n,1,l+2}],b'[R_]:>D[Sum[d[n] R^n,{n,1,l+2}],R],b''[R_]:>D[Sum[d[n] R^n,{n,1,l+2}],{R,2}]}/.d1rule[c,d,l,r]/.rules[r]],Log[1-2M/r]],r]];
If[First[cList]!=0||cList[[l+3+1]]!=0,Print["Error: first term not 0"];Abort[]];
cSol=Solve[cList==0,Join[Table[c[n],{n,2,l+3}],Table[d[n],{n,2,l+2}]]][[1]];
If[(Last[cList]/.cSol)!=0,Print["Error: solution not found"];Abort[]];
Collect[Log[1-2M/r]Sum[c[n] r^n,{n,2,l+3}]+Sum[d[n] r^n,{n,1,l+2}]/.d1rule[c,d,l,r]/.cSol,{C[4], C[5],Log[1-2M/r]}]]


M2afH[l_,r_]:=r^2 (1-2M/r) a1[l,r]+r M Log[(2M)/r]LegendreP[l,r/M-1] (C[1]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[2])/((-1+2 l) (1+2 l) (3+2 l))+C[3]\[Psi]0H[l,r];


M2af\[Infinity][l_,r_]:=a1\[Infinity][l,r]+r M PolyLog[2,(2 M)/r]LegendreP[l,r/M-1] (C[4]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[5])/( (-1+2 l) (1+2 l) (3+2 l))-r M Log[(2M)/r]LegendreQ[l,0,3,r/M-1] (C[4]-3/4 (-1+l)^3 l^2 (1+l)^2 (2+l)^3 C[5])/( (-1+2 l) (1+2 l) (3+2 l))+C[6]\[Psi]0\[Infinity][l,r]/.rules[r];


(* ::Section::Closed:: *)
(*Gauge invariant fields*)


\[Lambda][l_]:=1/2 (l-1)(l+2);


H0H[l_,r_]:=Module[{M2af=M2afH,\[Psi]0=Function[{ll,rr},C[1]\[Psi]0H[ll,rr]],\[Psi]2=Function[{ll,rr},C[2]\[Psi]2H[ll,rr]]},Collect[-((2 M M2af[l,r])/r^4)+(2 M D[M2af[l,r],r])/r^3+(M \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)-(M D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))+((3 (3+4 \[Lambda][l])M^3+15  \[Lambda][l](1+\[Lambda][l])M^2 r+4\[Lambda][l]^2 (1+\[Lambda][l]) M r^2 + \[Lambda][l]^2 (1+\[Lambda][l])^2 r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+((3+2 \[Lambda][l])M^2-2 \[Lambda][l] (1+\[Lambda][l]) M r+ \[Lambda][l] (1+\[Lambda][l]) r^2 )/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[1],C[2],C[3]},Simplify]];


H0\[Infinity][l_,r_]:=Module[{M2af=M2af\[Infinity],\[Psi]0=Function[{ll,rr},C[4]\[Psi]0\[Infinity][ll,rr]],\[Psi]2=Function[{ll,rr},C[5]\[Psi]2\[Infinity][ll,rr]]},Collect[-((2 M M2af[l,r])/r^4)+(2 M D[M2af[l,r],r])/r^3+(M \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)-(M D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))+((3 (3+4 \[Lambda][l])M^3+15  \[Lambda][l](1+\[Lambda][l])M^2 r+4\[Lambda][l]^2 (1+\[Lambda][l]) M r^2 + \[Lambda][l]^2 (1+\[Lambda][l])^2 r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+((3+2 \[Lambda][l])M^2-2 \[Lambda][l] (1+\[Lambda][l]) M r+ \[Lambda][l] (1+\[Lambda][l]) r^2 )/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[4],C[5],C[6]},Simplify]]


H1H[l_,r_]:=Module[{\[Psi]1=Function[{ll,rr},C[7]\[Psi]1H[ll,rr]]},Collect[-\[Psi]1[l,r]/r^2+M/((1+\[Lambda][l])r^2) D[\[Psi]1[l,r],r],{C[7]},Simplify]];


H1\[Infinity][l_,r_]:=Module[{\[Psi]1=Function[{ll,rr},C[8]\[Psi]1\[Infinity][ll,rr]]},Collect[-\[Psi]1[l,r]/r^2+M/((1+\[Lambda][l])r^2) D[\[Psi]1[l,r],r],{C[8]},Simplify]];


H2H[l_,r_]:=Module[{M2af=M2afH,\[Psi]0=Function[{ll,rr},C[1]\[Psi]0H[ll,rr]],\[Psi]2=Function[{ll,rr},C[2]\[Psi]2H[ll,rr]]},Collect[((6 M-4(2+\[Lambda][l])r) M2af[l,r])/r^4+((-6 M+4r) D[M2af[l,r],r])/r^3+((-3 M+2(2+\[Lambda][l])r)  \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)+((3M-2r) D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))-((9 (3+4 \[Lambda][l])M^3+3 \[Lambda][l](11+13\[Lambda][l])M^2 r+6\[Lambda][l](-1+\[Lambda][l]+2\[Lambda][l]^2) M r^2 + \[Lambda][l]^2 (-1+\[Lambda][l]^2)r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+(-3(3+2 \[Lambda][l])M^2+2 (3+\[Lambda][l] -\[Lambda][l]^2) M r+ \[Lambda][l] (1+\[Lambda][l]) r^2 )/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[1],C[2],C[3]},Simplify]];


H2\[Infinity][l_,r_]:=Module[{M2af=M2af\[Infinity],\[Psi]0=Function[{ll,rr},C[4]\[Psi]0\[Infinity][ll,rr]],\[Psi]2=Function[{ll,rr},C[5]\[Psi]2\[Infinity][ll,rr]]},Collect[((6 M-4(2+\[Lambda][l])r) M2af[l,r])/r^4+((-6 M+4r) D[M2af[l,r],r])/r^3+((-3 M+2(2+\[Lambda][l])r)  \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)+((3M-2r) D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))-((9 (3+4 \[Lambda][l])M^3+3 \[Lambda][l](11+13\[Lambda][l])M^2 r+6\[Lambda][l](-1+\[Lambda][l]+2\[Lambda][l]^2) M r^2 + \[Lambda][l]^2 (-1+\[Lambda][l]^2)r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+(-3(3+2 \[Lambda][l])M^2+2 (3+\[Lambda][l] -\[Lambda][l]^2) M r+ \[Lambda][l] (1+\[Lambda][l]) r^2 )/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[4],C[5],C[6]},Simplify]];


KH[l_,r_]:=Module[{M2af=M2afH,\[Psi]0=Function[{ll,rr},C[1]\[Psi]0H[ll,rr]],\[Psi]2=Function[{ll,rr},C[2]\[Psi]2H[ll,rr]]},Collect[((-4 M+2(2+\[Lambda][l])r) M2af[l,r])/r^4+((4 M-2r) D[M2af[l,r],r])/r^3-((r-2 M)  \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)+((r-2M) D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))+((6 (3+4 \[Lambda][l])M^3+3 \[Lambda][l](8+9\[Lambda][l])M^2 r+\[Lambda][l](-3+5\[Lambda][l]+8\[Lambda][l]^2) M r^2 + \[Lambda][l]^3 (1+\[Lambda][l])r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+((3+2 \[Lambda][l])M(2 M- r))/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[1],C[2],C[3]},Simplify]];


K\[Infinity][l_,r_]:=Module[{M2af=M2af\[Infinity],\[Psi]0=Function[{ll,rr},C[4]\[Psi]0\[Infinity][ll,rr]],\[Psi]2=Function[{ll,rr},C[5]\[Psi]2\[Infinity][ll,rr]]},Collect[((-4 M+2(2+\[Lambda][l])r) M2af[l,r])/r^4+((4 M-2r) D[M2af[l,r],r])/r^3-((r-2 M)  \[Psi]0[l,r])/(2(1+\[Lambda][l]) r^2)+((r-2M) D[\[Psi]0[l,r],r])/(2 r(1+ \[Lambda][l]))+((6 (3+4 \[Lambda][l])M^3+3 \[Lambda][l](8+9\[Lambda][l])M^2 r+\[Lambda][l](-3+5\[Lambda][l]+8\[Lambda][l]^2) M r^2 + \[Lambda][l]^3 (1+\[Lambda][l])r^3) \[Psi]2[l,r])/((1+\[Lambda][l]) r^2 (3 M+\[Lambda][l]r)^2)+((3+2 \[Lambda][l])M(2 M- r))/((1+ \[Lambda][l]) r (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[4],C[5],C[6]},Simplify]];


h0eH[l_,r_]:=Module[{\[Psi]1=Function[{ll,rr},C[7]\[Psi]1H[ll,rr]]},Collect[(2M-r)/(2r+2\[Lambda][l]r) D[\[Psi]1[l,r],r],{C[7]},Simplify]];


h0e\[Infinity][l_,r_]:=Module[{\[Psi]1=Function[{ll,rr},C[8]\[Psi]1\[Infinity][ll,rr]]},Collect[(2M-r)/(2r+2\[Lambda][l]r) D[\[Psi]1[l,r],r],{C[8]},Simplify]];


h1eH[l_,r_]:=Module[{M2af=M2afH,\[Psi]0=Function[{ll,rr},C[1]\[Psi]0H[ll,rr]],\[Psi]2=Function[{ll,rr},C[2]\[Psi]2H[ll,rr]]},Collect[(4 M2af[l,r])/r^2-(2 D[M2af[l,r],r])/r-  \[Psi]0[l,r]/(4(1+\[Lambda][l]) )+(r D[\[Psi]0[l,r],r])/(4(1+ \[Lambda][l]))-(\[Lambda][l](3M^2+6(1+\[Lambda][l])M r + \[Lambda][l] (1+\[Lambda][l])r^2) \[Psi]2[l,r])/(2(1+\[Lambda][l]) (3 M+\[Lambda][l]r)^2)-(r((6+5 \[Lambda][l])M+ \[Lambda][l] (1+\[Lambda][l])r))/(2(1+ \[Lambda][l]) (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[1],C[2],C[3]},Simplify]];


h1e\[Infinity][l_,r_]:=Module[{M2af=M2af\[Infinity],\[Psi]0=Function[{ll,rr},C[4]\[Psi]0\[Infinity][ll,rr]],\[Psi]2=Function[{ll,rr},C[5]\[Psi]2\[Infinity][ll,rr]]},Collect[(4 M2af[l,r])/r^2-(2 D[M2af[l,r],r])/r-  \[Psi]0[l,r]/(4(1+\[Lambda][l]) )+(r D[\[Psi]0[l,r],r])/(4(1+ \[Lambda][l]))-(\[Lambda][l](3M^2+6(1+\[Lambda][l])M r + \[Lambda][l] (1+\[Lambda][l])r^2) \[Psi]2[l,r])/(2(1+\[Lambda][l]) (3 M+\[Lambda][l]r)^2)-(r((6+5 \[Lambda][l])M+ \[Lambda][l] (1+\[Lambda][l])r))/(2(1+ \[Lambda][l]) (3 M+r \[Lambda][l])) D[\[Psi]2[l,r],r],{C[4],C[5],C[6]},Simplify]];


GH[l_,r_]:=Module[{M2af=M2afH,\[Psi]0=Function[{ll,rr},C[1]\[Psi]0H[ll,rr]],\[Psi]2=Function[{ll,rr},C[2]\[Psi]2H[ll,rr]]},Collect[-( M2af[l,r]/r^3),{C[1],C[2],C[3]},Simplify]];


G\[Infinity][l_,r_]:=Module[{M2af=M2af\[Infinity],\[Psi]0=Function[{ll,rr},C[4]\[Psi]0\[Infinity][ll,rr]],\[Psi]2=Function[{ll,rr},C[5]\[Psi]2\[Infinity][ll,rr]]},Collect[-( M2af[l,r]/r^3),{C[4],C[5],C[6]},Simplify]];


Trh[l,r_]:=Simplify[r(-H0[l,r]+H2[l,r]+2K[l,r])]


(* ::Section::Closed:: *)
(*Barack-Lousto-Sago homogeneous fields*)


h1H[l_,r_]:=(1-(2M)/r) r (H0H[l,r]+H2H[l,r]);
h2H[l_,r_]:=g[r] l(l+1) H1H[l,r];
h3H[l_,r_]:=2r (*(1-(2M)/r)*) KH[l,r];
h4H[l_,r_]:=2g[r] l(l+1) h0eH[l,r];
h5H[l_,r_]:=2(1-(2M)/r) l(l+1) h1eH[l,r];
h6H[l_,r_]:=r(H0H[l,r]-H2H[l,r]);
h7H[l_,r_]:=2r (l-1) l(l+1)(l+2) GH[l,r];


h1\[Infinity][l_,r_]:=(1-(2M)/r) r (H0\[Infinity][l,r]+H2\[Infinity][l,r]);
h3\[Infinity][l_,r_]:=2r (*(1-(2M)/r)*) K\[Infinity][l,r];
h5\[Infinity][l_,r_]:=2(1-(2M)/r) l(l+1) h1e\[Infinity][l,r];
h6\[Infinity][l_,r_]:=r(H0\[Infinity][l,r]-H2\[Infinity][l,r]);
h7\[Infinity][l_,r_]:=2r (l-1) l(l+1)(l+2) G\[Infinity][l,r];


(* ::Section:: *)
(*Inhomogeneous fields*)


M=1;
r0r = Rationalize[r0];
f0=1-2M/r0r;
\[CapitalOmega]\[Phi]=Sqrt[r0r^-3];
E0=f0 (1-3/r0r)^(-1/2);


LaunchKernels[];
SetSharedFunction[\[CapitalPhi]0, \[CapitalPhi]0inv, h1Left, h1Right, h3Left, h3Right, h5Left, h5Right, h6Left, h6Right, h7Left, h7Right, hstatic, dhstatic, ddhstatic];


ParallelDo[
Print["Computing \[CapitalPhi]0["<>ToString[l]<>"]"];
\[CapitalPhi]0[l]=Simplify[{Join[-Table[Coefficient[h1H[l,r],C[i]],{i,1,3}],Table[Coefficient[h1\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[Coefficient[h3H[l,r],C[i]],{i,1,3}],Table[Coefficient[h3\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[Coefficient[h5H[l,r],C[i]],{i,1,3}],Table[Coefficient[h5\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[D[Coefficient[h1H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h1\[Infinity][l,r],C[i]],r],{i,4,6}]],Join[-Table[D[Coefficient[h3H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h3\[Infinity][l,r],C[i]],r],{i,4,6}]],Join[-Table[D[Coefficient[h5H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h5\[Infinity][l,r],C[i]],r],{i,4,6}]]}/.r->r0r];
\[CapitalPhi]0inv[l]=Simplify[Inverse[\[CapitalPhi]0[l]]];,{l,lminret,lmaxret,2},Method->"FinestGrained"]


Do[
J1=-((16\[Pi] E0)/r0r)SphericalHarmonicY[l,0,\[Pi]/2,0];
J3=J1/f0;
J5=0;
source0={0,0,0,J1,J3,J5};
c[l]=\[CapitalPhi]0inv[l] . source0;,
{l,lminret,lmaxret,2}]


ParallelDo[
Print["Computing h1["<>ToString[l]<>"]"];
h1Left[l]=Simplify[h1H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h1Right[l]=Simplify[h1\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h3Left[l]=Simplify[h3H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h3Right[l]=Simplify[h3\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h5Left[l]=Simplify[h5H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h5Right[l]=Simplify[h5\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h6Left[l]=Simplify[h6H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h6Right[l]=Simplify[h6\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h7Left[l]=Simplify[h7H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h7Right[l]=Simplify[h7\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
,{l,lminret,lmaxret,2},Method->"FinestGrained"];


grid=Rationalize[Import[gridFile,{"Datasets","r"}],10^-10];
r0i=Import[gridFile,{"Datasets","ImportantIndexes"}][[2]];


ClearAll[hstatic,dhstatic,ddhstatic]


hstatic[i_Integer,l_,0] := hstatic[i,l,0] =
    Join[ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[Symbol["h"<>ToString[i]<>"Left"][l],$MachinePrecision]]],{r,grid[[;;r0i]]}],
         ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[Symbol["h"<>ToString[i]<>"Right"][l],$MachinePrecision]]],{r,grid[[r0i;;]]}]];


dhstatic[i_Integer,l_,0] := dhstatic[i,l,0] =
    Join[ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[D[Symbol["h"<>ToString[i]<>"Left"][l],r]/.r->R,$MachinePrecision]]],{R,grid[[;;r0i]]}],
         ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[D[Symbol["h"<>ToString[i]<>"Right"][l],r]/.r->R,$MachinePrecision]]],{R,grid[[r0i;;]]}]];


ddhstatic[i_Integer,l_,0] := ddhstatic[i,l,0] =
    Join[ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[D[Symbol["h"<>ToString[i]<>"Left"][l],r,r]/.r->R,$MachinePrecision]]],{R,grid[[;;r0i]]}],
         ParallelTable[Block[{$MaxExtraPrecision=\[Infinity](*10^5*)},N[N[D[Symbol["h"<>ToString[i]<>"Right"][l],r,r]/.r->R,$MachinePrecision]]],{R,grid[[r0i;;]]}]];


Do[Print["Computing hstatic["<>ToString[i]<>", "<>ToString[l]<>"]"];hstatic[i,l,0],{i,{1,3,5,6,7}},{l,lminret,lmaxret,2}]


Do[Print["Computing dhstatic["<>ToString[i]<>", "<>ToString[l]<>"]"];dhstatic[i,l,0],{i,{1,3,5,6,7}},{l,lminret,lmaxret,2}]


Do[Print["Computing ddhstatic["<>ToString[i]<>", "<>ToString[l]<>"]"];ddhstatic[i,l,0],{i,{1,3,5,6,7}},{l,lminret,lmaxret,2}]


Do[
hstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
hstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
dhstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
dhstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
ddhstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
ddhstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,2,0]]];
,{l,lminret,lmaxret}];


hretLeft[i_,l_,m_]:=hstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
hretRight[i_,l_,m_]:=hstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);
dhretLeft[i_,l_,m_]:=dhstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
dhretRight[i_,l_,m_]:=dhstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);
ddhretLeft[i_,l_,m_]:=ddhstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
ddhretRight[i_,l_,m_]:=ddhstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);


CreateDirectory[dataDir,CreateIntermediateDirectories->True];


Do[
Export[FileNameJoin[{dataDir,"h1-l"<>ToString[l]<>"m"<>ToString[m]<>".h5"}],{Transpose[{
Re[hretLeft[1,l,m]],Im[hretLeft[1,l,m]],Re[dhretLeft[1,l,m]],Im[dhretLeft[1,l,m]],Re[ddhretLeft[1,l,m]],Im[ddhretLeft[1,l,m]],
Re[hretLeft[3,l,m]],Im[hretLeft[3,l,m]],Re[dhretLeft[3,l,m]],Im[dhretLeft[3,l,m]],Re[ddhretLeft[3,l,m]],Im[ddhretLeft[3,l,m]],
Re[hretLeft[5,l,m]],Im[hretLeft[5,l,m]],Re[dhretLeft[5,l,m]],Im[dhretLeft[5,l,m]],Re[ddhretLeft[5,l,m]],Im[ddhretLeft[5,l,m]],
Re[hretLeft[6,l,m]],Im[hretLeft[6,l,m]],Re[dhretLeft[6,l,m]],Im[dhretLeft[6,l,m]],Re[ddhretLeft[6,l,m]],Im[ddhretLeft[6,l,m]],
Re[hretLeft[7,l,m]],Im[hretLeft[7,l,m]],Re[dhretLeft[7,l,m]],Im[dhretLeft[7,l,m]],Re[ddhretLeft[7,l,m]],Im[ddhretLeft[7,l,m]],
Re[hretLeft[2,l,m]],Im[hretLeft[2,l,m]],Re[dhretLeft[2,l,m]],Im[dhretLeft[2,l,m]],Re[ddhretLeft[2,l,m]],Im[ddhretLeft[2,l,m]],
Re[hretLeft[4,l,m]],Im[hretLeft[4,l,m]],Re[dhretLeft[4,l,m]],Im[dhretLeft[4,l,m]],Re[ddhretLeft[4,l,m]],Im[ddhretLeft[4,l,m]]}],Transpose[{
Re[hretRight[1,l,m]],Im[hretRight[1,l,m]],Re[dhretRight[1,l,m]],Im[dhretRight[1,l,m]],Re[ddhretRight[1,l,m]],Im[ddhretRight[1,l,m]],
Re[hretRight[3,l,m]],Im[hretRight[3,l,m]],Re[dhretRight[3,l,m]],Im[dhretRight[3,l,m]],Re[ddhretRight[3,l,m]],Im[ddhretRight[3,l,m]],
Re[hretRight[5,l,m]],Im[hretRight[5,l,m]],Re[dhretRight[5,l,m]],Im[dhretRight[5,l,m]],Re[ddhretRight[5,l,m]],Im[ddhretRight[5,l,m]],
Re[hretRight[6,l,m]],Im[hretRight[6,l,m]],Re[dhretRight[6,l,m]],Im[dhretRight[6,l,m]],Re[ddhretRight[6,l,m]],Im[ddhretRight[6,l,m]],
Re[hretRight[7,l,m]],Im[hretRight[7,l,m]],Re[dhretRight[7,l,m]],Im[dhretRight[7,l,m]],Re[ddhretRight[7,l,m]],Im[ddhretRight[7,l,m]],
Re[hretRight[2,l,m]],Im[hretRight[2,l,m]],Re[dhretRight[2,l,m]],Im[dhretRight[2,l,m]],Re[ddhretRight[2,l,m]],Im[ddhretRight[2,l,m]],
Re[hretRight[4,l,m]],Im[hretRight[4,l,m]],Re[dhretRight[4,l,m]],Im[dhretRight[4,l,m]],Re[ddhretRight[4,l,m]],Im[ddhretRight[4,l,m]]}],grid},
{"Datasets",{"inhom_left","inhom_right","grid"}}];,{l,lminret,lmaxret,2},{m,{0}}];
