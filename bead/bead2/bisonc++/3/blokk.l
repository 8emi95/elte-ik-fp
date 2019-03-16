%option noyywrap c++

%{
#include "Parserbase.h"
%}

WS	[ \t\n]

%%

skip	return Parser::SKIP;
begin	return Parser::KEZDET;
end	return Parser::VEG;

{WS}+	// feher szokozok: semmi teendo

. {
	std::cerr << "lexikalis hiba" << std::endl;
	return 0;
}

%%
