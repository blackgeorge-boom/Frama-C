/*
 * This file can be successfully verified using Frama-C with Jessie plugin.
 *   Frama-C Carbon-20110201
 *   Alt-Ergo 0.92.2 / Simplify 1.5.7 / CVC3 2.2
 */

#include "max.h"

int max (int x, int y) {
    return (x >= y) ? x : y;
}
