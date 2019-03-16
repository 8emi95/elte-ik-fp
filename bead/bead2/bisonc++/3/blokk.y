%baseclass-preinclude <iostream>

%token SKIP KEZDET VEG
%%

start:
	program
;

program:
	// ures
|
	SKIP program
|
	blokk program
;

blokk:
	KEZDET program VEG
;
