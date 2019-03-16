%baseclass-preinclude <iostream>

%token AZONOSITO NYITO CSUKO VESSZO PONTOSVESSZO
%%

start:
	deklaracioLista
;

deklaracioLista:
	// ures
|
	deklaracio deklaracioLista
;

deklaracio:
	AZONOSITO AZONOSITO parameterek PONTOSVESSZO
;

parameterek:
	NYITO lista CSUKO
;

lista:
	// ures
|
	AZONOSITO AZONOSITO folytatas
;

folytatas:
	// ures
|
	VESSZO AZONOSITO AZONOSITO folytatas
;
