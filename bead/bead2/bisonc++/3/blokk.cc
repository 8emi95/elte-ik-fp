#include <iostream>
#include <fstream>
#include <sstream>
#include "Parser.h"
#include <FlexLexer.h>

using namespace std;

int main( int argc, char* argv[] )
{
	if( argc != 2 )
	{
		cerr << "Egy parancssori argumentum kell!" << endl;
		return 1;
	}
	ifstream in( argv[1] );
	if( !in )
	{
		cerr << "Nem tudom megnyitni: " << argv[1] << endl;
		return 1;
	}
	
	Parser pars(in);
	pars.parse();
	return 0;
}
