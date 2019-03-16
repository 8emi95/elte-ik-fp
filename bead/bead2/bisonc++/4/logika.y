%baseclass-preinclude <iostream>

%token IGAZ HAMIS NYITO CSUKO AZONOSITO
%right EKV
%right IMPL
%left VAGY
%left ES
%right NEM

%%

start:
	formula
;

formula:
	IGAZ
|
	HAMIS
|
	AZONOSITO
|
	NYITO formula CSUKO
|
	formula EKV formula
|
	formula IMPL formula
|
	formula VAGY formula
|
	formula ES formula
|
	NEM formula
;
