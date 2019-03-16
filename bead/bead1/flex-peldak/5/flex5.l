%option noyywrap c++

%{
#include <iostream>
#include <fstream>

using namespace std;

int sor=1,oszlop=1;
%}

%%

[^\n\t ]+	{
			cout << sor << ' ' << oszlop << ' ' << YYText() << endl;
			oszlop += YYLeng();
		}

\n		{
			++sor;
			oszlop=1;
		}

.			++oszlop;

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
