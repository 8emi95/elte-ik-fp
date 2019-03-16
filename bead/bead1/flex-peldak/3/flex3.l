%option noyywrap c++

%{
#include <iostream>
#include <fstream>

using namespace std;
%}

%%

\t	cout << "&nbsp;";

\n	cout << "<BR>" << endl;

\<	cout << "&lt;";

\>	cout << "&gt;";

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
