%baseclass-preinclude <iostream>
%lsp-needed

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
|
	error PONTOSVESSZO
	{
		std::cerr << "\t- hibas deklaracio"  << std::endl;
	}
;

parameterek:
	NYITO lista CSUKO
|
	NYITO error CSUKO
	{
		std::cerr << "\t- hiba a parameterlistaban"  << std::endl;
	}
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
