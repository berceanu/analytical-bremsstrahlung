#!/usr/bin/env wolframscript
(* ::Package:: *)

(* ::Input::Initialization:: *)
$Assumptions={Element[{n},Integers],n>0,t>0,0<k<\[Epsilon]0,k<\[Epsilon]<\[Epsilon]0,b>1,0<tp<t,0<\[Mu]<1};


(* ::Input::Initialization:: *)
ClearAll[timeAvg]
SetAttributes[timeAvg,HoldFirst] (*profiling function*)
timeAvg[func_]:=Do[If[#>0.3,Return[#/5^i]]&@@Timing@Do[func,{5^i}],{i,0,15}]


(* ::Input::Initialization:: *)
ClearAll[distributeH,contractH,distributeInt,distributeSum,contractInt,contractSum]
distributeH[H_,expr_]:=With[{rules={ (* rules for distributing integrals and factoring out constants *)
Inactive[H][f_+g_,it:{x_Symbol,__}]:>Inactive[H][f,it]+Inactive[H][g,it],
Inactive[H][c_ f_,it:{x_Symbol,__}]:>c Inactive[H][f,it]/;FreeQ[c,x],
Inactive[H][c_,it:{x_Symbol,__}]:>c Inactive[H][1,it]/;FreeQ[c,x]
}},
expr//.rules]
contractH[H_,expr_]:=With[{rules={ (* rules for conctacting sums and factoring in constants *)
c_ Inactive[H][1,it:{x_Symbol,__}]/;FreeQ[c,x]:> Inactive[H][c,it],
c_ Inactive[H][f_,it:{x_Symbol,__}]/;FreeQ[c,x]:> Inactive[H][c f,it],
Inactive[H][f_,it1:{_Symbol,__}]+Inactive[H][g_,it2:{_Symbol,__}]/;it1== it2:>Inactive[H][f+g,it1]
}},
expr//.rules]
distributeInt[expr_]:=distributeH[Integrate,expr]
distributeSum[expr_]:=distributeH[Sum,expr]
contractInt[expr_]:=contractH[Integrate,expr]
contractSum[expr_]:=contractH[Sum,expr]


(* ::Input::Initialization:: *)
ClearAll[changeSign,changeVar,byParts]
changeSign[Inactive[Integrate][f_,{x_Symbol,x1_,x2_}]]:=Inactive[Integrate][-f,{x,x2,x1}] (*flip integration limits*)
changeVar[Inactive[Integrate][f_,{x_Symbol,x1_,x2_}],{u_,sub:(x_->gu_)}]:=With[{integrand=(f/.sub) D[gu,u],
u1=u/.First@Normal@Solve[gu==x1,u,Reals],
u2=u/.First@Normal@Solve[gu==x2,u,Reals]},
Inactive[Integrate][integrand,{u,u1,u2}]
(*change integration variable*)]
(*symbolic integration by parts*)
byParts[Inactive[Integrate][integrand_,{var_Symbol,l_,h_}], dv_]:=Module[{u,v,du},
u =  Expand[integrand/dv];
du =D[u,var];
v =Normal@Integrate[dv,var];
Simplify[ReplaceAll[var->h][u v]]-Simplify[ReplaceAll[var->l][u v]]-Inactive[Integrate][du v,{var,l,h}]
]


(* ::Input::Initialization:: *)
ClearAll[flipSumInt,flipAllSumInt]
flipSumInt[ Inactive[Integrate][Inactive[Sum][expr_,domsum:{_Symbol,_,_}],domint:{_Symbol,_,_}] ] :=Inactive[Sum][Inactive[Integrate][expr,domint],domsum]
flipAllSumInt[expr_]:=Module[{integrals = Cases[expr,Inactive[Integrate][_,{var_Symbol,_,_}]/;var==x,\[Infinity]]},
expr/.Thread[Rule[integrals,flipSumInt/@integrals]]]


(* ::Input::Initialization:: *)
ClearAll[applytoContent,applytoHead,applytoInt,applytoSum,applytoContentInt,applytoContentSum]
applytoContent[expr_,head_,var_][foo_]:=expr/.Inactive[head][content_,dom:{v_Symbol,_,_}]/;v==var:> Inactive[head][foo[content],dom]
(* example usage: applytoContent[doubleint,Sum,n][Simplify[#]&]*)
applytoHead[expr_,head_,var_][foo_]:=expr/.Inactive[head][content_,dom:{v_Symbol,_,_}]/;v==var:> foo[Inactive[head][content,dom]]
(* example usage: applytoHead[doubleint,Integrate,x][contractH[Integrate,#]&]*)
applytoInt[expr_,var_][foo_]:=applytoHead[expr,Integrate,var][foo]
applytoSum[expr_,var_][foo_]:=applytoHead[expr,Sum,var][foo]
applytoContentInt[expr_,var_][foo_]:=applytoContent[expr,Integrate,var][foo]
applytoContentSum[expr_,var_][foo_]:=applytoContent[expr,Sum,var][foo]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
ClearAll[\[Rho]BN,I\[Gamma]approx]
\[Rho]BN[A_,k_,na_,X0_,r0_,t_,Z_,\[Alpha]_,\[Epsilon]_]:=na/A X0 (4 \[Alpha] r0^2 Z^2) t/k (1-(2 (-k+\[Epsilon]))/(3 \[Epsilon])+(-k+\[Epsilon])^2/\[Epsilon]^2) (-(1/2)+Log[(2 \[Epsilon] (-k+\[Epsilon]))/k])
I\[Gamma]approx[\[Epsilon]_,k_,t_]:=(1/k) ((-E^(-7 t/9)+(1-k/\[Epsilon])^(4 t/3))/(7/9+4/3 Log[1-k/\[Epsilon]]))(*Subscript[[Subscript[I, \[Gamma]]], approx]*)


(* ::Input::Initialization:: *)
ClearAll[Ie,\[Rho],I\[Gamma],I\[Gamma]0,doubleint0]
Ie[t_,\[Epsilon]_,\[Epsilon]0_,b_]:=1/\[Epsilon]0 (Log[\[Epsilon]0/\[Epsilon]])^(b t-1)/Gamma[b t]
\[Rho][\[Epsilon]_,k_]:=1/k (4/3 (1-k/\[Epsilon])+(k/\[Epsilon])^2)(1+1/9 (1-k/\[Epsilon])C1); (* {1 \[Rule] na/AX0 (4 \[Alpha] Subscript[r, 0]^2)(Z^2(Lrad[Z]-f[Z])+Z Lradp[Z]), C1\[Rule] (na/AX0 )(4 \[Alpha] r0^2)(Z^2+Z) } *)
I\[Gamma]0[t_,k_,\[Epsilon]0_,b_,\[Mu]_]:=Inactive[Integrate][Inactive[Integrate][Exp[-\[Mu](t-tp)] Ie[tp,\[Epsilon],\[Epsilon]0,b] \[Rho][\[Epsilon],k],{\[Epsilon],k,\[Epsilon]0}],{tp,0,t}]


(* ::Input::Initialization:: *)
doubleint0=I\[Gamma]0[t,k,\[Epsilon]0,b,\[Mu]];ClearAll[\[Rho],I\[Gamma]0];


(* ::Input::Initialization:: *)
doubleint1=applytoInt[doubleint0,\[Epsilon]][distributeInt[#]&];
doubleint2 = applytoInt[doubleint1,tp][distributeInt[#]&];


(* ::Text:: *)
(*We first focus on the inner integral over energy. The integral has a divergence when b tp < 1 and \[Epsilon] = \[Epsilon]0. We make the change of variable  \[Epsilon] = \[Epsilon]0 E^-x and flip the integration limits.*)


(* ::Input::Initialization:: *)
doubleint3=applytoInt[doubleint2,\[Epsilon]][changeSign@changeVar[#,{x,\[Epsilon]-> \[Epsilon]0 E^-x}]&]/.Log[Power[E,a_]]/;Internal`DependsOnQ[a,x]:> a;


(* ::Text:: *)
(*We now integrate by parts, \[Integral]f \[DifferentialD]g=f g -\[Integral]g \[DifferentialD]f, with dg = x^(-1+b tp) .*)


(* ::Input::Initialization:: *)
dg=First@Cases[doubleint3,Power[x,_],\[Infinity]]


(* ::Input::Initialization:: *)
doubleint4=applytoInt[doubleint3,x][byParts[#, dg]&];


(* ::Text:: *)
(*We now insert the infinite series expansion for the exponentials.*)


(* ::Input::Initialization:: *)
doubleint5=doubleint4/.Exp[a_]/;Internal`DependsOnQ[a,x]:> Inactive[Sum][Power[a,n]/Factorial[n],{n,0,\[Infinity]}] ;


(* ::Text:: *)
(*Change order of sums and integrals.*)


(* ::Input::Initialization:: *)
doubleint6=applytoContentInt[doubleint5,x][Expand[#]&];


(* ::Input::Initialization:: *)
doubleint7=  applytoInt[doubleint6,x][distributeInt[#]&];
doubleint8= contractSum[#]&@doubleint7;


(* ::Input::Initialization:: *)
doubleint9=flipAllSumInt[#]&@doubleint8;


(* ::Text:: *)
(*Perform the integrations over x.*)


(* ::Input::Initialization:: *)
doubleint10=applytoInt[doubleint9,x][Activate[#]&];


(* ::Input::Initialization:: *)
doubleint11= contractSum[#]&@doubleint10; (* factor out the sum *)
doubleint12= applytoContentSum[doubleint11,n][Simplify[#]&];(* simplify the summand *)
doubleint13=contractInt[#]&@doubleint12; (* pull everything inside the integral *)
doubleint14= applytoContentInt[doubleint13,tp][Apart@distributeSum[#]&]; (* pull out constants from the sum  and divide by numerator*)
doubleint15=applytoSum[doubleint14,n][Simplify@Activate[#]&]; (* perform the summation analytically; in case this is not possible one can do it numerically, truncating after first 20 terms *)



(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
ClearAll[I\[Gamma],doubleint,tmp] 
doubleint :=doubleint15/.Integrate-> NIntegrate
Block[{t,k,\[Epsilon]0,b,\[Mu],C1},
tmp[t_,k_,\[Epsilon]0_,b_,\[Mu]_,C1_]=doubleint;
I\[Gamma][t_?NumericQ,k_?NumericQ,\[Epsilon]0_?NumericQ,b_?NumericQ,\[Mu]_?NumericQ,C1_?NumericQ]:=Activate[#,NIntegrate]&@tmp[t,k,\[Epsilon]0,b,\[Mu],C1];
]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
ClearAll[withRules,config]
SetAttributes[withRules,HoldAll]
withRules[rules_,expr_]:=First@PreemptProtect@Internal`InheritedBlock[{Rule,RuleDelayed},SetAttributes[{Rule,RuleDelayed},HoldFirst];
Hold[expr]/.rules]
withRules[config[rules___],expr_]:=withRules[{rules},expr]
config[newrules__]@config[rules__]:=config[newrules,rules]
ClearAll[listofConfigs]
listofConfigs[expr_]:=With[{substitutions={List[config[rules1__],config[rules2__],seq___]:> List[config[rules1]@config[rules2],seq],
List[config[rules__]]:> config[rules]}}, expr//.substitutions]
(* example usage *)
old=config[par1->val1,par2->val2];new=config[par1->val3,par2->val4];total=new@old;
withRules[Evaluate[new@old],par1+par2]
ClearAll[old,new]
listofConfigs[{config[a-> b],config[c-> d],config[e-> f],config[g-> h]}]


(* ::Input::Initialization:: *)
ClearAll[constants]
constants = config[mc2->UnitConvert[Quantity["ElectronMass"]*Quantity["SpeedOfLight"]^2,"Megaelectronvolts"] ,na->UnitConvert[Quantity["AvogadroConstant"]] ,\[Alpha]->1/137 ,r0->UnitConvert[Quantity["ClassicalElectronRadius"],"Centimeters"] ]


(* ::Input::Initialization:: *)
ClearAll[Lrad,Lradp,b,f,X0,T]
Lrad[Z_?NumericQ]:=Log[184.15 Z^(-(1/3))]; (*1/4(\[Phi]10-4/3Log[Z])/; {\[Phi]10=20.863,\[Psi]10=28.340}*)
Lradp[Z_?NumericQ]:=Log[1194. Z^(-(2/3))]; (*1/4(\[Psi]10-8/3Log[Z])*)
b[Z_?NumericQ]:=4/3 (1+1/12 (Z^2+Z)/(Z^2 Lrad[Z]+Z Lradp[Z]));
f[Z_?NumericQ,\[Alpha]_]:=f[Z]=N@Re[HarmonicNumber[I Z \[Alpha]]];
X0[A_,na_,r0_,Z_?NumericQ,\[Alpha]_]:= A/(4 na r0^2 Z \[Alpha] (-Z f[Z,\[Alpha]]+Z Lrad[Z]+Lradp[Z]));
t[L_, \[Rho]_, A_,na_,r0_,Z_?NumericQ,\[Alpha]_] :=(L \[Rho])/X0[A,na,r0,Z,\[Alpha]]; (* thickness in units of radiation lengths *)
C1[A_,na_,r0_,Z_?NumericQ,\[Alpha]_]:= (na/A X0[A,na,r0,Z,\[Alpha]] )(4 \[Alpha] r0^2)(Z^2+Z); 
(*\[Mu][]:=*)


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
ClearAll[elementData]
elementData[element_]/;StringQ[element]:=config[Z ->  ElementData[element,"AtomicNumber"],A-> UnitConvert[ElementData[element,"AtomicWeight"]Quantity["AvogadroConstant"],"Grams"/"Moles"],\[Rho]-> UnitConvert[ElementData[element,"Density"],"Grams"/"Centimeters"^3]]
elementData["Tungsten"]


(* ::Input::Initialization:: *)
ClearAll[addFunctiontoRules]
addFunctiontoRules[oldrules_,foo_[args__]]:=withRules[Evaluate@oldrules, config[foo-> foo[args]]]
addFunctiontoRules[constants,f[A,na,r0,Z,\[Alpha]]]


(* ::Input::Initialization:: *)
ClearAll[allData,tungsten,aluminium]
allData[element_,thickness_]/;StringQ[element]:=With[{edata=elementData[element],L=thickness},config[elem-> element]@edata@(addFunctiontoRules[constants@edata,#]&/@{b[Z],X0[A,na,r0,Z,\[Alpha]],C1[A,na,r0,Z,\[Alpha]],t[L, \[Rho], A,na,r0,Z,\[Alpha]]}//listofConfigs)]

tungsten=allData["Tungsten",Quantity[3.5,"Millimeters"]]
aluminum=allData["Aluminum",Quantity[1,"Micrometers"]]


(* ::Input::Initialization:: *)
ClearAll[elements,photonEn,table]
elements={"Hydrogen" ,"Helium" ,"Lithium" ,"Beryllium","Carbon","Nitrogen","Neon","Aluminum","Iron","Copper","Tin","Tungsten","Lead","Uranium"};
photonEn=Quantity[#,"Gigaelectronvolts"]&/@{100,10,6,2,1,0.6,0.4,0.2,0.1};
table=Transpose@Partition[{0.011,0.012,0.004,0.003,0.002,0.002,0.002,0.002,0.001,0.001,0.001,0.001,0.001,0.001,0.028,0.023,0.024,0.020,0.016,0.015,0.012,0.011,0.009,0.009,0.008,0.007,0.007,0.007,0.039,0.030,0.034,0.029,0.023,0.022,0.019,0.017,0.014,0.013,0.012,0.011,0.011,0.011,0.079,0.058,0.073,0.064,0.053,0.050,0.044,0.040,0.033,0.032,0.029,0.028,0.028,0.028,0.126,0.091,0.113,0.101,0.087,0.082,0.073,0.068,0.057,0.056,0.051,0.049,0.049,0.048,0.174,0.128,0.154,0.139,0.122,0.116,0.105,0.098,0.084,0.082,0.075,0.073,0.072,0.072,0.222,0.166,0.195,0.178,0.158,0.151,0.137,0.129,0.112,0.110,0.102,0.099,0.098,0.098,0.323,0.253,0.283,0.263,0.238,0.230,0.213,0.202,0.180,0.177,0.166,0.162,0.162,0.162,0.441,0.367,0.391,0.370,0.343,0.334,0.315,0.302,0.275,0.272,0.259,0.256,0.257,0.258},Length@elements];
TableForm[table,TableHeadings->{elements,photonEn}] ;(* table III.5 from Rev.Mod.Phys. 46(4) 1974 *)
ClearAll[\[Xi],\[Mu]]
\[Xi][elem_,k_]/;StringQ[elem]&&QuantityQ[k]&&QuantityUnit[k]=="Gigaelectronvolts":=With[{lines=Thread[Rule[elements,Range@Length@elements]],
columns=Thread[Rule[photonEn,Range@Length@photonEn]]},
l=elem/.lines;
c=First@Nearest[photonEn,k,1]/.columns;
(* Print[First@Nearest[photonEn,k,1]]; *)
table[[l,c]]
]
\[Mu][elem_,k_]/;StringQ[elem]&&QuantityQ[k]:=With[{kGeV=UnitConvert[k,"Gigaelectronvolts"]},7/9 (1-\[Xi][elem,kGeV])]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[k-> 200(*mc^2*),\[Epsilon]0-> 1000]@constants@aluminum),
Plot[k I\[Gamma][T,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1],{T,0,4},FrameLabel->{Style["radiation length",20]},ImageSize->600,AspectRatio->1,PlotTheme->{"Monochrome","VibrantColor","Detailed"}]]


(* ::Input:: *)
(**)


(* ::Section:: *)
(*Computing the total number of photons for the Aluminium case*)


(* ::Input::Initialization:: *)
Module[{Qe,Ne},
Qe=Quantity[10,"Nanocoulombs"];(* total charge *) 
Ne=Qe/UnitConvert[Quantity["ElementaryCharge"],"Nanocoulombs"]; (*number of electrons*) 
electrons=config[ne-> Ne,q-> Qe]; 
]


(* ::Text:: *)
(*According to arXiv:1803.08237, the total number of produced photons from the GEANT4 simulation is 1.75 10^7.*)


(* ::Subsection:: *)
(*Using Subscript[\[Rho], BN]*)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]-> 1000]@electrons@constants@aluminum),
ne * NIntegrate[\[Rho]BN[A,k,na,X0,r0,t,Z,\[Alpha],\[Epsilon]] ,{k,0.01,100}]
](* compared to 2.54x10^7 value from arxiv paper *)


(* ::Input::Initialization:: *)
withRules[Evaluate@constants,100 mc2]


(* ::Subsection:: *)
(*Using Subscript[I, \[Gamma]]*)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0-> 1000]@electrons@constants@aluminum),
ne *NIntegrate[I\[Gamma][t,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1],{k,0.01,100}]
]


(* ::Input::Initialization:: *)
% * 2 (* factor 2 difference from GEANT result *)


(* ::Subsection:: *)
(*Plotting Subscript[\[Rho], BN] and Subscript[I, \[Gamma]] on the same graph*)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0-> 1000(*mc^2*),t-> 1.6]@electrons@constants@aluminum),
Plot[{ne * \[Rho]BN[A,k,na,X0,r0,t,Z,\[Alpha],\[Epsilon]0],ne * I\[Gamma][t,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1]},{k,0.01,\[Epsilon]0},
FrameLabel->{Style["k(\!\(\*SuperscriptBox[\(mc\), \(2\)]\))",20],Style["no photons",20]},
ImageSize->600,
AspectRatio->1,
PlotTheme->{"Monochrome","VibrantColor","Detailed"}]]


(* ::Subsection:: *)
(*What happens if we consider a thicker target?*)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0-> 1000,k-> 200]@electrons@constants@aluminum),
ne *I\[Gamma][t,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1]
](*number of photons at k = 200 mc^2 energy for 1 \[Mu]m target thickness*)



(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0-> 1000,k-> 200,t-> 1.6]@electrons@constants@aluminum),
{(t X0)/\[Rho],ne *I\[Gamma][t,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1]}
](*number of photons at k = 200 mc^2 energy for 14 cm target thickness*)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0-> 1000,t-> 8/5]@electrons@constants@aluminum),
ne *NIntegrate[I\[Gamma][t,k,\[Epsilon]0,b,\[Mu][elem,k mc2],C1],{k,0.01,\[Epsilon]0-1},MaxPoints->500000,WorkingPrecision->5,PrecisionGoal->3]
](* total number of photons for 14 cm target thickness *)



(* ::Subsection:: *)
(*Adding a finite bandwidth to the electron distribution*)


(* ::Input::Initialization:: *)
withRules[Evaluate@constants,
toGamma[energy_]/;QuantityQ[energy]:=energy/mc2;
toMeV[gamma_?NumericQ]:=gamma * mc2;]
toGamma[Quantity[260,"Megaelectronvolts"]];
toMeV[100]; (* example usage *)


(* ::Input::Initialization:: *)
ClearAll[spectrumElectrons,\[Epsilon]L,\[Epsilon]H]
spectrumElectrons[\[Epsilon]_,\[Epsilon]0_,f_]:=1/(f \[Epsilon]0) HeavisideTheta[1/4-((\[Epsilon]-\[Epsilon]0)/(f \[Epsilon]0))^2];
{\[Epsilon]L[\[Epsilon]0_,f_],\[Epsilon]H[\[Epsilon]0_,f_]}=\[Epsilon]/.Normal@Solve[Cases[spectrumElectrons[\[Epsilon],\[Epsilon]0,f],HeavisideTheta[x_]-> x==0],\[Epsilon],Reals]//Expand[#]&//Collect[#,\[Epsilon]0]&;


(* ::Input::Initialization:: *)
sol=First@Solve[{\[Epsilon]L[\[Epsilon]0,f]==1/100,\[Epsilon]H[\[Epsilon]0,f]==260},{f,\[Epsilon]0}];


(* ::Input::Initialization:: *)
With[{\[Epsilon]0=Quantity[\[Epsilon]0/.sol,"MeV"]//toGamma, f=f/.sol, offset = Quantity[100,"MeV"]//toGamma},
Plot[spectrumElectrons[\[Epsilon],\[Epsilon]0,f],{\[Epsilon],\[Epsilon]L[\[Epsilon]0,f]-offset,\[Epsilon]H[\[Epsilon]0,f]+offset},
FrameLabel->{Style["\[Epsilon](\!\(\*SuperscriptBox[\(mc\), \(2\)]\))",20]},
Exclusions->None,
GridLines->{{{\[Epsilon]0,Red}},None},
PlotTheme->{"Monochrome","VibrantColor","Detailed"},
ImageSize->600]]


(* ::Input:: *)
(**)


(* ::Input::Initialization:: *)
withRules[Evaluate@(config[\[Epsilon]0->254,f-> 2,ne-> 8.7 10^9]@constants@tungsten),
 ne/(f \[Epsilon]0)*NIntegrate[ I\[Gamma][t,k,\[Epsilon],b,\[Mu][elem,toMeV@k],C1],{\[Epsilon],\[Epsilon]L[\[Epsilon]0,f]+1,\[Epsilon]H[\[Epsilon]0,f]-1},{k,0.01,\[Epsilon]-1},
MaxPoints->500000,WorkingPrecision->5,PrecisionGoal->3]] (* == ne*NIntegrate[I\[Gamma][t,k,\[Epsilon]prime,b,\[Mu][elem,toMeV@k],C1],{k,0.01,\[Epsilon]prime-1}], with \[Epsilon]L < \[Epsilon]prime < \[Epsilon]H according to the mean-value theorem *)


(* ::Input:: *)
(*(*TODO: change variables to spectrumElectrons[\[Epsilon]0,\[Epsilon]c,f] and change %126*)*)
