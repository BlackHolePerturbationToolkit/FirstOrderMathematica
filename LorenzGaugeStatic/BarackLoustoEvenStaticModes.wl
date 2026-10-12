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
(* timing of each phase (master) and of each parallel job (subkernels), for profiling *)
phaseT0=AbsoluteTime[]; phase[name_]:=(Print["phase ",name,": ",Round[AbsoluteTime[]-phaseT0,0.1]," s"]; phaseT0=AbsoluteTime[]);
SetSharedFunction[\[CapitalPhi]0, \[CapitalPhi]0inv, h1Left, h1Right, h3Left, h3Right, h5Left, h5Right, h6Left, h6Right, h7Left, h7Right];


ParallelDo[
Print["Computing \[CapitalPhi]0["<>ToString[l]<>"]"];
With[{t0=AbsoluteTime[]},
\[CapitalPhi]0[l]=Simplify[{Join[-Table[Coefficient[h1H[l,r],C[i]],{i,1,3}],Table[Coefficient[h1\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[Coefficient[h3H[l,r],C[i]],{i,1,3}],Table[Coefficient[h3\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[Coefficient[h5H[l,r],C[i]],{i,1,3}],Table[Coefficient[h5\[Infinity][l,r],C[i]],{i,4,6}]],Join[-Table[D[Coefficient[h1H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h1\[Infinity][l,r],C[i]],r],{i,4,6}]],Join[-Table[D[Coefficient[h3H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h3\[Infinity][l,r],C[i]],r],{i,4,6}]],Join[-Table[D[Coefficient[h5H[l,r],C[i]],r],{i,1,3}],Table[D[Coefficient[h5\[Infinity][l,r],C[i]],r],{i,4,6}]]}/.r->r0r];
\[CapitalPhi]0inv[l]=Simplify[Inverse[\[CapitalPhi]0[l]]]; Print["  Phi0[",l,"]: ",Round[AbsoluteTime[]-t0,0.1]," s"]];,{l,lminret,lmaxret,2},Method->"FinestGrained"];
phase["Phi0"]


Do[
J1=-((16\[Pi] E0)/r0r)SphericalHarmonicY[l,0,\[Pi]/2,0];
J3=J1/f0;
J5=0;
source0={0,0,0,J1,J3,J5};
c[l]=\[CapitalPhi]0inv[l] . source0;,
{l,lminret,lmaxret,2}];
phase["constants"]


ParallelDo[
Print["Computing h1["<>ToString[l]<>"]"];
With[{t0=AbsoluteTime[]},
h1Left[l]=Simplify[h1H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h1Right[l]=Simplify[h1\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h3Left[l]=Simplify[h3H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h3Right[l]=Simplify[h3\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h5Left[l]=Simplify[h5H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h5Right[l]=Simplify[h5\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h6Left[l]=Simplify[h6H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h6Right[l]=Simplify[h6\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h7Left[l]=Simplify[h7H[l,r]/.{M->1,C[i_]:>c[l][[i]]}];
h7Right[l]=Simplify[h7\[Infinity][l,r]/.{M->1,C[i_]:>c[l][[i]]}]; Print["  closed forms l = ",l,": ",Round[AbsoluteTime[]-t0,0.1]," s"]];
,{l,lminret,lmaxret,2},Method->"FinestGrained"];
phase["closed forms"]


grid=Rationalize[Import[gridFile,{"Datasets","r"}],10^-10];
r0i=Import[gridFile,{"Datasets","ImportantIndexes"}][[2]];


(* Second radial derivatives are optional: they follow from the field equations (and the h1S code of
   the second-order pipeline computes them there), so outputSecondDerivatives=False saves a third of the
   evaluation and writes 4 columns per field (h, dh) instead of 6 (h, dh, ddh). *)
If[!BooleanQ[outputSecondDerivatives],outputSecondDerivatives=True];


(* One parallel job per field and l: the closed form is fetched once from the master kernel, its
   derivatives are taken once, and all grid points are evaluated locally on the subkernel. (Evaluating
   points as separate parallel tasks through the shared functions sends the large expressions back
   and forth for every point and dominated the run time.) The closed forms cancel strongly at high l
   and large r, hence 60 digits with up to 2000 digits of extra precision. *)
ClearAll[hstatic,dhstatic,ddhstatic];
(* Each closed form is numericised once at working precision wp (its exact rationals and surds would make the
   point-by-point evaluation several hundred times slower) and evaluated on blocks of consecutive grid points as
   arrays. The closed forms cancel strongly (outside the orbit a solution decaying like r^-(l+1) is the difference of
   much larger terms: hundreds of digits at the outer grid points), and the precision needed varies smoothly along the
   grid, so each block starts at the precision the previous block ended with; points where precision tracking reports
   fewer than 18 digits (or, for values that cancel to ~0, an accuracy below 40) are redone at twice the precision
   (staticEvalExact, the original point-by-point evaluation, beyond 8192 digits). *)
staticEvalExact[ex_,pts_]:=Block[{$MaxExtraPrecision=2000},Table[N[N[ex/.r->R,60]],{R,pts}]];
staticEval[ex_,pts_]:=Module[{wp0=60,out=ConstantArray[0.,Length[pts]],fs=<||>,f,blocks},
  (* numericised closed form at each working precision; substituted with /. (inserting ex into Function[{r}, ...]
     would rename the bound r and leave the closed form unevaluated) *)
  f[wp_]:=If[KeyExistsQ[fs,wp],fs[wp],fs[wp]=N[ex,wp+10]];
  blocks=Partition[Range[Length[pts]],UpTo[200]];
  Do[Module[{idx=blk,wp=wp0,v,ok},
      While[idx=!={}&&wp<=8192,
        v=f[wp]/.r->SetPrecision[pts[[idx]],wp+10];
        If[!ListQ[v],v=ConstantArray[v,Length[idx]]];
        ok=Map[NumericQ[#]&&(Precision[#]>=18||Accuracy[#]>=40)&,v];
        out[[Pick[idx,ok]]]=N[Pick[v,ok]];
        idx=Pick[idx,ok,False];If[idx=!={},wp*=2]];
      If[idx=!={},out[[idx]]=staticEvalExact[ex,pts[[idx]]]];
      wp0=wp],
    {blk,blocks}];
  out];
staticJob[i_,l_]:=Module[{t0=AbsoluteTime[],exL=Symbol["h"<>ToString[i]<>"Left"][l],exR=Symbol["h"<>ToString[i]<>"Right"][l],nd=If[outputSecondDerivatives,2,1],t1,res},
  t1=AbsoluteTime[];
  res=Table[Join[staticEval[D[exL,{r,n}],grid[[;;r0i]]],staticEval[D[exR,{r,n}],grid[[r0i;;]]]],{n,0,nd}];
  Print["  grid h",i,"[",l,"]: fetch ",Round[t1-t0,0.1]," s, evaluate ",Round[AbsoluteTime[]-t1,0.1]," s"]; res];
staticJobs=Reverse[Flatten[Table[{i,l},{l,lminret,lmaxret,2},{i,{1,3,5,6,7}}],1]];
staticResults=ParallelMap[(Print["Computing static modes of h"<>ToString[#[[1]]]<>", l = "<>ToString[#[[2]]]];staticJob@@#)&,staticJobs,Method->"FinestGrained"];
MapThread[(hstatic[#1[[1]],#1[[2]],0]=#2[[1]];dhstatic[#1[[1]],#1[[2]],0]=#2[[2]];
  If[outputSecondDerivatives,ddhstatic[#1[[1]],#1[[2]],0]=#2[[3]]])&,{staticJobs,staticResults}];
Clear[staticResults];
phase["grid evaluation"]


Do[
hstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
hstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
dhstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
dhstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
ddhstatic[2,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
ddhstatic[4,l,0]=ConstantArray[0.+0.I,Length[hstatic[1,lminret,0]]];
,{l,lminret,lmaxret}];


hretLeft[i_,l_,m_]:=hstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
hretRight[i_,l_,m_]:=hstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);
dhretLeft[i_,l_,m_]:=dhstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
dhretRight[i_,l_,m_]:=dhstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);
ddhretLeft[i_,l_,m_]:=ddhstatic[i,l,m][[;;r0i]](*/._[___,Left,___]\[Rule]0*);
ddhretRight[i_,l_,m_]:=ddhstatic[i,l,m][[r0i+1;;]](*/._[___,Right,___]\[Rule]0*);


CreateDirectory[dataDir,CreateIntermediateDirectories->True];


(* Expansion about the horizon of each field, h(r) = sum_n c_n (r - 2M)^n (static, so no phase
   factor), from the closed forms inside the orbit: dataset "horizon" with row n and the real and
   imaginary parts of each field in the order of inhom_left (as written by h1Lorenz). *)
horizonTerms=12;
SetSharedFunction[horizonTable];
ParallelDo[
horizonTable[l]=Module[{x,cs,t0=AbsoluteTime[]},
cs=Table[If[MemberQ[{2,4},i],ConstantArray[0,horizonTerms],
PadRight[CoefficientList[Normal[Series[Symbol["h"<>ToString[i]<>"Left"][l]/.r->2+x,{x,0,horizonTerms-1}]],x],horizonTerms]],{i,{1,3,5,6,7,2,4}}];
cs=N[N[cs,40]]; Print["  horizon series l = ",l,": ",Round[AbsoluteTime[]-t0,0.1]," s"];
Transpose[Flatten[Table[{Re[cs[[k]]],Im[cs[[k]]]},{k,Length[cs]}],1]]];
,{l,lminret,lmaxret,2},Method->"FinestGrained"];
phase["horizon series"]


(* Expansion at infinity of each field, h(r) = sum_n (b_n + c_n log r)/r^n, from the closed forms
   outside the orbit: datasets "infinity" (b_n) and "infinity_log" (c_n), row n, Re/Im of each
   field in the order of inhom_right (as written by h1Lorenz). *)
SetSharedFunction[infinityTable];
ParallelDo[
infinityTable[l]=Module[{y,Lr,cs,s,t0=AbsoluteTime[]},
cs=Table[If[MemberQ[{2,4},i],ConstantArray[{0,0},horizonTerms],
s=Normal[Series[Symbol["h"<>ToString[i]<>"Right"][l]/.r->1/y,{y,0,horizonTerms-1}]]/.Log[y]->-Lr;
If[!FreeQ[s,y^_?Negative]||!FreeQ[s,Log[y]],Print["unexpected terms in the expansion at infinity of h",i,"[",l,"]"]];
Table[{Coefficient[s,y,n]/.Lr->0,Coefficient[Coefficient[s,y,n],Lr]},{n,0,horizonTerms-1}]],{i,{1,3,5,6,7,2,4}}];
cs=N[N[cs,40]]; Print["  infinity series l = ",l,": ",Round[AbsoluteTime[]-t0,0.1]," s"];
Table[Transpose[Flatten[Table[{Re[cs[[k,All,part]]],Im[cs[[k,All,part]]]},{k,Length[cs]}],1]],{part,2}]];
,{l,lminret,lmaxret,2},Method->"FinestGrained"];
phase["infinity series"]


staticColumns[hs_,l_,m_]:=Flatten[Table[{Re[#],Im[#]}&/@If[outputSecondDerivatives,{hs[[1]][i,l,m],hs[[2]][i,l,m],hs[[3]][i,l,m]},{hs[[1]][i,l,m],hs[[2]][i,l,m]}],{i,{1,3,5,6,7,2,4}}],2];
Do[
Export[FileNameJoin[{dataDir,"h1-l"<>ToString[l]<>"m"<>ToString[m]<>".h5"}],{Transpose[staticColumns[{hretLeft,dhretLeft,ddhretLeft},l,m]],
Transpose[staticColumns[{hretRight,dhretRight,ddhretRight},l,m]],grid,horizonTable[l],infinityTable[l][[1]],infinityTable[l][[2]]},
{"Datasets",{"inhom_left","inhom_right","grid","horizon","infinity","infinity_log"}}];,{l,lminret,lmaxret,2},{m,{0}}];
phase["export"]
