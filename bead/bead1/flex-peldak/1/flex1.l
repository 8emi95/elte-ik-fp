%option noyywrap c++

%{
#include <iostream>
#include <fstream>

using namespace std;
%}

%%

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
