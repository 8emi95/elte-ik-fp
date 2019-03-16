#ifndef SEMANTICS_H
#define SEMANTICS_H

#include <string>
#include <iostream>
#include <sstream>

enum tipus { Egesz, Logikai, Ido_t };

struct valtozo_leiro
{
	int def_sora;
	tipus vtip;
	std::string cimke;
	valtozo_leiro( int s = 0, tipus t = Egesz, int sz = 0 )
		: def_sora(s), vtip(t)
	{
		std::stringstream out;
		out << "Cimke" << sz;
		cimke = out.str();
	}
};

struct kifejezes_leiro
{
	int sor;
	tipus ktip;
	std::string kod;
	kifejezes_leiro( int s, tipus t, std::string k )
		: sor(s), ktip(t), kod(k) {}
};

struct utasitas_leiro
{
	int sor;
	std::string kod;
	utasitas_leiro( int s, std::string k )
		: sor(s), kod(k) {}
};


#endif //SEMANTICS_H
