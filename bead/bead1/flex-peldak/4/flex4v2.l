%option noyywrap c++

%{
#include <iostream>
#include <fstream>

using namespace std;

int sor=1;
%}

%%

[^\n]*\n	{
			cout << sor << ' ' << YYLeng() << endl;
			++sor;
		}

.		// semmi

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
