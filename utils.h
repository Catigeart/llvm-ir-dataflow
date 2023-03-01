//
// Created by catigeart on 2022/12/11.
//

#ifndef ASSIGN3_UTILS_H
#define ASSIGN3_UTILS_H

// #define DEBUG

#ifdef DEBUG
#define DEBUG_LOG(msg)                                                         \
  do {                                                                         \
    errs() << "\u001b[33m[DEBUG] \u001b[0m" << msg << "\n";                                       \
  } while (0)
#else
#define DEBUG_LOG(msg)                                                         \
  do {                                                                         \
  } while (0)
#endif

#endif //ASSIGN3_UTILS_H
