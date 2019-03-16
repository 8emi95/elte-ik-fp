%option noyywrap c++

%{
#include "Parserbase.h"
%}

SZAMJEGY	[0-9]
BETU		[a-zA-Z]
WS		[ \t\n]

%%

true				return Parser::IGAZ;
false				return Parser::HAMIS;
"("				return Parser::NYITO;
")"				return Parser::CSUKO;
"&"				return Parser::ES;
"|"				return Parser::VAGY;
"!"				return Parser::NEM;
"->"				return Parser::IMPL;
"<->"				return Parser::EKV;
{BETU}({BETU}|{SZAMJEGY})*	return Parser::AZONOSITO;

{WS}+	// feher szokozok: semmi teendo

. {
	std::cerr << "lexikalis hiba" << std::endl;
	return 0;
}

%%
