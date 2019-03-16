%option noyywrap c++

%{
#include <iostream>
#include <fstream>

using namespace std;
%}

%%

username	cout << "deva";

%%

int main()
{
	ifstream in("input.txt");
	yyFlexLexer fl( &in, &cout );
	fl.yylex();
	return 0;
}
