%option noyywrap c++ yylineno

%{
#include <iostream>
#include <fstream>

using namespace std;

int oszlop=1;
%}

%%

[^\n\t ]+	{
			cout << lineno() << ' ' << oszlop << ' ' << YYText() << endl;
			oszlop += YYLeng();
		}

\n			oszlop=1;

.			++oszlop;

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
