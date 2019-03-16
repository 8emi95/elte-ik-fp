%baseclass-preinclude <iostream>

%token ELEM NYITO CSUKO VESSZO
%%

start:
	NYITO lista CSUKO
;

lista:
	// ures
|
	ELEM folytatas
;

folytatas:
	// ures
|
	VESSZO ELEM folytatas
;
