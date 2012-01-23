/*
 *   TinyScheme OOPS (Object Oriented Programming System) extension version 0.1
 * for TinyScheme 1.38 
 *
 * (c) 2007 Sergey Cherepanov (s-cherepanov@users.sourceforge.net)
 */

#include "scheme-private.h"

static pointer set_closure_environment(scheme *sc, pointer args)
{
	if (sc->vptr->is_pair(args)) {
		pointer p1 = sc->vptr->pair_car(args);

		if (sc->vptr->is_closure(p1)) {
			pointer p2 = sc->vptr->pair_cdr(args);

			if (sc->vptr->pair_cdr(p2) == sc->NIL) {
				pointer p3 = sc->vptr->pair_car(p2);

				if (sc->vptr->is_environment(p3)) {
					sc->vptr->set_cdr(p1, p3);
					return sc->T;
				}
			}
		}
	}
	return sc->F;
}

#undef cons

static pointer copy_list(scheme *sc, pointer l)
{
	if (sc->vptr->is_pair(l)) {
		pointer car = sc->NIL, cdr = sc->NIL;

		car = copy_list(sc, sc->vptr->pair_car(l));
		cdr = copy_list(sc, sc->vptr->pair_cdr(l));
		l = sc->vptr->cons(sc, car, cdr);
	}
	return l;
}

#define settype(p,t) (p)->_flag=((p)->_flag&~31)|t

static pointer environment_to_list(scheme *sc, pointer arg)
{
	pointer e = sc->vptr->pair_car(arg);

	if (sc->vptr->is_environment(e)) {
		pointer l;

		settype(e, 5); /* T_PAIR */
		l = copy_list(sc, e);
		settype(e, 14); /* T_ENVIRONMENT */
		return l;
	}
	return sc->NIL;
}

SCHEME_EXPORT void init_oops(scheme *sc)
{
	sc->vptr->scheme_define(sc, sc->global_env,
		sc->vptr->mk_symbol(sc, "set-closure-environment!"),
		sc->vptr->mk_foreign_func(sc, set_closure_environment));
	sc->vptr->scheme_define(sc, sc->global_env,
		sc->vptr->mk_symbol(sc, "environment->list"),
		sc->vptr->mk_foreign_func(sc, environment_to_list));
}
