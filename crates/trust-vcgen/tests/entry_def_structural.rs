// Trust: THE DEFINITION SEAM, end to end.
//
// A PARAMETER is defined at ENTRY, implicitly; `body.blocks` never carries that
// definition. Three rounds of site-by-site patching left the class open because each
// round fixed the sites it enumerated. `trust_vcgen::local_defs` is now the ONLY place
// that scans blocks for a local's definitions, and every caller asks a question that
// already knows about the entry definition — see that module's doc for the mechanism
// by which a fact keyed on a two-valued bare name empties a path and proves everything
// on it.
//
// Every `MIR_*` below is the compiler's OWN extracted verification input, captured
// verbatim from the PRISTINE 70a7534fd1 stage2 with
//
//   trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> <file>.rs
//
// against the source named on each constant. They are embedded INLINE rather than
// dropped in `tests/fixtures/` on purpose: a corpus-derived obligation count is
// ratcheted elsewhere and this lane must not perturb it.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

const MIR_PARAM_MOD_DIVISOR_GUARDED: &str = r##"{
  "name": "param_mod_divisor_guarded",
  "def_path": "w::param_mod_divisor_guarded",
  "span": {
    "file": "w.rs",
    "line_start": 2,
    "col_start": 0,
    "line_end": 4,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "a"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "m"
      },
      {
        "index": 3,
        "ty": "Bool",
        "name": "c"
      },
      {
        "index": 4,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 5,
        "ty": "Bool",
        "name": null
      },
      {
        "index": 6,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 7,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 8,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 9,
        "ty": "Bool",
        "name": null
      },
      {
        "index": 10,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Copy": {
                "local": 3,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                2
              ]
            ],
            "otherwise": 1,
            "exhaustive_enum_unreachable": false,
            "span": {
              "file": "w.rs",
              "line_start": 3,
              "col_start": 7,
              "line_end": 3,
              "col_end": 8
            }
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 2,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      4,
                      64
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 11,
                "line_end": 3,
                "col_end": 16
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 23,
                "line_end": 3,
                "col_end": 24
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Eq",
                  {
                    "Move": {
                      "local": 6,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        0,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 23,
                "line_end": 3,
                "col_end": 29
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 5,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                4
              ]
            ],
            "otherwise": 3,
            "exhaustive_enum_unreachable": false,
            "span": {
              "file": "w.rs",
              "line_start": 3,
              "col_start": 23,
              "line_end": 3,
              "col_end": 29
            }
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      0,
                      8
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 39,
                "line_end": 3,
                "col_end": 40
              }
            }
          }
        ],
        "terminator": {
          "Goto": 7
        }
      },
      {
        "id": 4,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 8,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 56,
                "line_end": 3,
                "col_end": 57
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 9,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Eq",
                  {
                    "Copy": {
                      "local": 8,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        0,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 52,
                "line_end": 3,
                "col_end": 57
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 9,
                "projections": []
              }
            },
            "expected": false,
            "msg": "RemainderByZero",
            "target": 5,
            "span": {
              "file": "w.rs",
              "line_start": 3,
              "col_start": 52,
              "line_end": 3,
              "col_end": 57
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 5,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 7,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Rem",
                  {
                    "Copy": {
                      "local": 1,
                      "projections": []
                    }
                  },
                  {
                    "Move": {
                      "local": 8,
                      "projections": []
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 52,
                "line_end": 3,
                "col_end": 57
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 10,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 7,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 59,
                "line_end": 3,
                "col_end": 65
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 10,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 6,
            "span": {
              "file": "w.rs",
              "line_start": 3,
              "col_start": 59,
              "line_end": 3,
              "col_end": 65
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 6,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 4,
                    "projections": [
                      "Deref",
                      {
                        "Index": 7
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 3,
                "col_start": 59,
                "line_end": 3,
                "col_end": 65
              }
            }
          }
        ],
        "terminator": {
          "Goto": 7
        }
      },
      {
        "id": 7,
        "stmts": [],
        "terminator": "Return"
      }
    ],
    "arg_count": 4,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "m",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "m",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_PARAM_MIN_ARG: &str = r##"{
  "name": "param_min_arg",
  "def_path": "w::param_min_arg",
  "span": {
    "file": "w.rs",
    "line_start": 5,
    "col_start": 0,
    "line_end": 7,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "a"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "b"
      },
      {
        "index": 3,
        "ty": "Bool",
        "name": "c"
      },
      {
        "index": 4,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 5,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "n"
      },
      {
        "index": 6,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 7,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Copy": {
                "local": 3,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                2
              ]
            ],
            "otherwise": 1,
            "exhaustive_enum_unreachable": false,
            "span": {
              "file": "w.rs",
              "line_start": 6,
              "col_start": 7,
              "line_end": 6,
              "col_end": 8
            }
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 2,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      3,
                      64
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 6,
                "col_start": 11,
                "line_end": 6,
                "col_end": 16
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 6,
                "col_start": 34,
                "line_end": 6,
                "col_end": 35
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<usize as core::cmp::Ord>::min",
            "args": [
              {
                "Copy": {
                  "local": 1,
                  "projections": []
                }
              },
              {
                "Move": {
                  "local": 6,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 5,
              "projections": []
            },
            "target": 3,
            "span": {
              "file": "w.rs",
              "line_start": 6,
              "col_start": 28,
              "line_end": 6,
              "col_end": 36
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 7,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 5,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 6,
                "col_start": 38,
                "line_end": 6,
                "col_end": 44
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 7,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 4,
            "span": {
              "file": "w.rs",
              "line_start": 6,
              "col_start": 38,
              "line_end": 6,
              "col_end": 44
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 4,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 4,
                    "projections": [
                      "Deref",
                      {
                        "Index": 5
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 6,
                "col_start": 38,
                "line_end": 6,
                "col_end": 44
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 4,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "b",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "b",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U64_ACC_PARAM: &str = r##"{
  "name": "u64_acc_param",
  "def_path": "w::u64_acc_param",
  "span": {
    "file": "w.rs",
    "line_start": 8,
    "col_start": 0,
    "line_end": 10,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "t"
      },
      {
        "index": 2,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 64
              }
            }
          }
        },
        "name": "a"
      },
      {
        "index": 3,
        "ty": "Bool",
        "name": "c"
      },
      {
        "index": 4,
        "ty": {
          "Adt": {
            "name": "core::slice::iter::Iter",
            "fields": [
              [
                "ptr",
                {
                  "Adt": {
                    "name": "core::ptr::non_null::NonNull",
                    "fields": [
                      [
                        "pointer",
                        {
                          "RawPtr": {
                            "mutable": false,
                            "pointee": {
                              "Int": {
                                "width": 8,
                                "signed": false
                              }
                            }
                          }
                        }
                      ]
                    ],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ],
              [
                "end_or_len",
                {
                  "RawPtr": {
                    "mutable": false,
                    "pointee": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ],
              [
                "_marker",
                {
                  "Adt": {
                    "name": "core::marker::PhantomData",
                    "fields": [],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Adt": {
            "name": "core::slice::iter::Iter",
            "fields": [
              [
                "ptr",
                {
                  "Adt": {
                    "name": "core::ptr::non_null::NonNull",
                    "fields": [
                      [
                        "pointer",
                        {
                          "RawPtr": {
                            "mutable": false,
                            "pointee": {
                              "Int": {
                                "width": 8,
                                "signed": false
                              }
                            }
                          }
                        }
                      ]
                    ],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ],
              [
                "end_or_len",
                {
                  "RawPtr": {
                    "mutable": false,
                    "pointee": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ],
              [
                "_marker",
                {
                  "Adt": {
                    "name": "core::marker::PhantomData",
                    "fields": [],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": "iter"
      },
      {
        "index": 6,
        "ty": {
          "Adt": {
            "name": "core::option::Option",
            "fields": [
              [
                "__tag",
                {
                  "Int": {
                    "width": 64,
                    "signed": true
                  }
                }
              ],
              [
                "__v1_0",
                {
                  "Ref": {
                    "mutable": false,
                    "inner": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ]
            ],
            "variants": [
              {
                "name": "None",
                "discriminant": 0,
                "fields": []
              },
              {
                "name": "Some",
                "discriminant": 1,
                "fields": [
                  [
                    "0",
                    {
                      "Ref": {
                        "mutable": false,
                        "inner": {
                          "Int": {
                            "width": 8,
                            "signed": false
                          }
                        }
                      }
                    }
                  ]
                ]
              }
            ],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Enum"
          }
        },
        "name": null
      },
      {
        "index": 7,
        "ty": {
          "Ref": {
            "mutable": true,
            "inner": {
              "Adt": {
                "name": "core::slice::iter::Iter",
                "fields": [
                  [
                    "ptr",
                    {
                      "Adt": {
                        "name": "core::ptr::non_null::NonNull",
                        "fields": [
                          [
                            "pointer",
                            {
                              "RawPtr": {
                                "mutable": false,
                                "pointee": {
                                  "Int": {
                                    "width": 8,
                                    "signed": false
                                  }
                                }
                              }
                            }
                          ]
                        ],
                        "variants": [],
                        "disc_index_safe": false,
                        "faithful_enum_repr": null,
                        "layout": null,
                        "enum_layout": null,
                        "adt_kind": "Struct"
                      }
                    }
                  ],
                  [
                    "end_or_len",
                    {
                      "RawPtr": {
                        "mutable": false,
                        "pointee": {
                          "Int": {
                            "width": 8,
                            "signed": false
                          }
                        }
                      }
                    }
                  ],
                  [
                    "_marker",
                    {
                      "Adt": {
                        "name": "core::marker::PhantomData",
                        "fields": [],
                        "variants": [],
                        "disc_index_safe": false,
                        "faithful_enum_repr": null,
                        "layout": null,
                        "enum_layout": null,
                        "adt_kind": "Struct"
                      }
                    }
                  ]
                ],
                "variants": [],
                "disc_index_safe": false,
                "faithful_enum_repr": null,
                "layout": null,
                "enum_layout": null,
                "adt_kind": "Struct"
              }
            }
          }
        },
        "name": null
      },
      {
        "index": 8,
        "ty": {
          "Int": {
            "width": 64,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 9,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": "x"
      },
      {
        "index": 10,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 11,
        "ty": {
          "Tuple": [
            {
              "Int": {
                "width": 64,
                "signed": false
              }
            },
            "Bool"
          ]
        },
        "name": null
      },
      {
        "index": 12,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Int": {
                "width": 8,
                "signed": false
              }
            }
          }
        },
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Copy": {
                "local": 3,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                2
              ]
            ],
            "otherwise": 1,
            "exhaustive_enum_unreachable": false,
            "span": {
              "file": "w.rs",
              "line_start": 9,
              "col_start": 7,
              "line_end": 9,
              "col_end": 8
            }
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      0,
                      64
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 11,
                "line_end": 9,
                "col_end": 16
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      },
      {
        "id": 2,
        "stmts": [],
        "terminator": {
          "Call": {
            "func": "<&[u8; 64] as core::iter::traits::collect::IntoIterator>::into_iter",
            "args": [
              {
                "Copy": {
                  "local": 2,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 4,
              "projections": []
            },
            "target": 3,
            "span": {
              "file": "w.rs",
              "line_start": 9,
              "col_start": 30,
              "line_end": 9,
              "col_end": 31
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 4,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 30,
                "line_end": 9,
                "col_end": 31
              }
            }
          }
        ],
        "terminator": {
          "Goto": 4
        }
      },
      {
        "id": 4,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 7,
                "projections": []
              },
              "rvalue": {
                "Ref": {
                  "mutable": true,
                  "place": {
                    "local": 5,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 30,
                "line_end": 9,
                "col_end": 31
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::slice::iter::Iter<'_, u8> as core::iter::traits::iterator::Iterator>::next",
            "args": [
              {
                "Copy": {
                  "local": 7,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 6,
              "projections": []
            },
            "target": 5,
            "span": {
              "file": "w.rs",
              "line_start": 9,
              "col_start": 30,
              "line_end": 9,
              "col_end": 31
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 5,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 8,
                "projections": []
              },
              "rvalue": {
                "Discriminant": {
                  "local": 6,
                  "projections": []
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 30,
                "line_end": 9,
                "col_end": 31
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 8,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                8
              ],
              [
                1,
                7
              ]
            ],
            "otherwise": 6,
            "exhaustive_enum_unreachable": true,
            "span": {
              "file": "w.rs",
              "line_start": 9,
              "col_start": 30,
              "line_end": 9,
              "col_end": 31
            }
          }
        }
      },
      {
        "id": 6,
        "stmts": [],
        "terminator": "Unreachable"
      },
      {
        "id": 7,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 12,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 6,
                    "projections": [
                      {
                        "Downcast": 1
                      },
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 25,
                "line_end": 9,
                "col_end": 26
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 9,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 12,
                    "projections": [
                      "Deref"
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 25,
                "line_end": 9,
                "col_end": 26
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 10,
                "projections": []
              },
              "rvalue": {
                "Cast": [
                  {
                    "Copy": {
                      "local": 9,
                      "projections": []
                    }
                  },
                  {
                    "Int": {
                      "width": 64,
                      "signed": false
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 39,
                "line_end": 9,
                "col_end": 47
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 11,
                "projections": []
              },
              "rvalue": {
                "CheckedBinaryOp": [
                  "Add",
                  {
                    "Copy": {
                      "local": 1,
                      "projections": []
                    }
                  },
                  {
                    "Copy": {
                      "local": 10,
                      "projections": []
                    }
                  }
                ]
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 34,
                "line_end": 9,
                "col_end": 47
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 11,
                "projections": [
                  {
                    "Field": 1
                  }
                ]
              }
            },
            "expected": false,
            "msg": {
              "Overflow": "Add"
            },
            "target": 9,
            "span": {
              "file": "w.rs",
              "line_start": 9,
              "col_start": 34,
              "line_end": 9,
              "col_end": 47
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 8,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 51,
                "line_end": 9,
                "col_end": 52
              }
            }
          }
        ],
        "terminator": "Return"
      },
      {
        "id": 9,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 11,
                    "projections": [
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "w.rs",
                "line_start": 9,
                "col_start": 34,
                "line_end": 9,
                "col_end": 47
              }
            }
          }
        ],
        "terminator": {
          "Goto": 4
        }
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 64,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "Or": [
        {
          "Eq": [
            {
              "Var": [
                "_8",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Eq": [
            {
              "Var": [
                "_8",
                "Int"
              ]
            },
            {
              "Int": 1
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "t",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "t",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U64_ACC: &str = r##"{
  "name": "u64_acc",
  "def_path": "wide_unsigned_accumulator::u64_acc",
  "span": {
    "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
    "line_start": 9,
    "col_start": 0,
    "line_end": 15,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 64
              }
            }
          }
        },
        "name": "a"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "t"
      },
      {
        "index": 3,
        "ty": {
          "Adt": {
            "name": "core::slice::iter::Iter",
            "fields": [
              [
                "ptr",
                {
                  "Adt": {
                    "name": "core::ptr::non_null::NonNull",
                    "fields": [
                      [
                        "pointer",
                        {
                          "RawPtr": {
                            "mutable": false,
                            "pointee": {
                              "Int": {
                                "width": 8,
                                "signed": false
                              }
                            }
                          }
                        }
                      ]
                    ],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ],
              [
                "end_or_len",
                {
                  "RawPtr": {
                    "mutable": false,
                    "pointee": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ],
              [
                "_marker",
                {
                  "Adt": {
                    "name": "core::marker::PhantomData",
                    "fields": [],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 4,
        "ty": {
          "Adt": {
            "name": "core::slice::iter::Iter",
            "fields": [
              [
                "ptr",
                {
                  "Adt": {
                    "name": "core::ptr::non_null::NonNull",
                    "fields": [
                      [
                        "pointer",
                        {
                          "RawPtr": {
                            "mutable": false,
                            "pointee": {
                              "Int": {
                                "width": 8,
                                "signed": false
                              }
                            }
                          }
                        }
                      ]
                    ],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ],
              [
                "end_or_len",
                {
                  "RawPtr": {
                    "mutable": false,
                    "pointee": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ],
              [
                "_marker",
                {
                  "Adt": {
                    "name": "core::marker::PhantomData",
                    "fields": [],
                    "variants": [],
                    "disc_index_safe": false,
                    "faithful_enum_repr": null,
                    "layout": null,
                    "enum_layout": null,
                    "adt_kind": "Struct"
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": "iter"
      },
      {
        "index": 5,
        "ty": {
          "Adt": {
            "name": "core::option::Option",
            "fields": [
              [
                "__tag",
                {
                  "Int": {
                    "width": 64,
                    "signed": true
                  }
                }
              ],
              [
                "__v1_0",
                {
                  "Ref": {
                    "mutable": false,
                    "inner": {
                      "Int": {
                        "width": 8,
                        "signed": false
                      }
                    }
                  }
                }
              ]
            ],
            "variants": [
              {
                "name": "None",
                "discriminant": 0,
                "fields": []
              },
              {
                "name": "Some",
                "discriminant": 1,
                "fields": [
                  [
                    "0",
                    {
                      "Ref": {
                        "mutable": false,
                        "inner": {
                          "Int": {
                            "width": 8,
                            "signed": false
                          }
                        }
                      }
                    }
                  ]
                ]
              }
            ],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Enum"
          }
        },
        "name": null
      },
      {
        "index": 6,
        "ty": {
          "Ref": {
            "mutable": true,
            "inner": {
              "Adt": {
                "name": "core::slice::iter::Iter",
                "fields": [
                  [
                    "ptr",
                    {
                      "Adt": {
                        "name": "core::ptr::non_null::NonNull",
                        "fields": [
                          [
                            "pointer",
                            {
                              "RawPtr": {
                                "mutable": false,
                                "pointee": {
                                  "Int": {
                                    "width": 8,
                                    "signed": false
                                  }
                                }
                              }
                            }
                          ]
                        ],
                        "variants": [],
                        "disc_index_safe": false,
                        "faithful_enum_repr": null,
                        "layout": null,
                        "enum_layout": null,
                        "adt_kind": "Struct"
                      }
                    }
                  ],
                  [
                    "end_or_len",
                    {
                      "RawPtr": {
                        "mutable": false,
                        "pointee": {
                          "Int": {
                            "width": 8,
                            "signed": false
                          }
                        }
                      }
                    }
                  ],
                  [
                    "_marker",
                    {
                      "Adt": {
                        "name": "core::marker::PhantomData",
                        "fields": [],
                        "variants": [],
                        "disc_index_safe": false,
                        "faithful_enum_repr": null,
                        "layout": null,
                        "enum_layout": null,
                        "adt_kind": "Struct"
                      }
                    }
                  ]
                ],
                "variants": [],
                "disc_index_safe": false,
                "faithful_enum_repr": null,
                "layout": null,
                "enum_layout": null,
                "adt_kind": "Struct"
              }
            }
          }
        },
        "name": null
      },
      {
        "index": 7,
        "ty": {
          "Int": {
            "width": 64,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 8,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": "x"
      },
      {
        "index": 9,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 10,
        "ty": {
          "Tuple": [
            {
              "Int": {
                "width": 64,
                "signed": false
              }
            },
            "Bool"
          ]
        },
        "name": null
      },
      {
        "index": 11,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Int": {
                "width": 8,
                "signed": false
              }
            }
          }
        },
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 2,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      0,
                      64
                    ]
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 10,
                "col_start": 21,
                "line_end": 10,
                "col_end": 22
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<&[u8; 64] as core::iter::traits::collect::IntoIterator>::into_iter",
            "args": [
              {
                "Copy": {
                  "local": 1,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 3,
              "projections": []
            },
            "target": 1,
            "span": {
              "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
              "line_start": 11,
              "col_start": 14,
              "line_end": 11,
              "col_end": 15
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 3,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 11,
                "col_start": 14,
                "line_end": 11,
                "col_end": 15
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "Ref": {
                  "mutable": true,
                  "place": {
                    "local": 4,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 11,
                "col_start": 14,
                "line_end": 11,
                "col_end": 15
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::slice::iter::Iter<'_, u8> as core::iter::traits::iterator::Iterator>::next",
            "args": [
              {
                "Copy": {
                  "local": 6,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 5,
              "projections": []
            },
            "target": 3,
            "span": {
              "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
              "line_start": 11,
              "col_start": 14,
              "line_end": 11,
              "col_end": 15
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 7,
                "projections": []
              },
              "rvalue": {
                "Discriminant": {
                  "local": 5,
                  "projections": []
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 11,
                "col_start": 14,
                "line_end": 11,
                "col_end": 15
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 7,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                6
              ],
              [
                1,
                5
              ]
            ],
            "otherwise": 4,
            "exhaustive_enum_unreachable": true,
            "span": {
              "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
              "line_start": 11,
              "col_start": 14,
              "line_end": 11,
              "col_end": 15
            }
          }
        }
      },
      {
        "id": 4,
        "stmts": [],
        "terminator": "Unreachable"
      },
      {
        "id": 5,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 11,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 5,
                    "projections": [
                      {
                        "Downcast": 1
                      },
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 11,
                "col_start": 9,
                "line_end": 11,
                "col_end": 10
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 8,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 11,
                    "projections": [
                      "Deref"
                    ]
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 11,
                "col_start": 9,
                "line_end": 11,
                "col_end": 10
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 9,
                "projections": []
              },
              "rvalue": {
                "Cast": [
                  {
                    "Copy": {
                      "local": 8,
                      "projections": []
                    }
                  },
                  {
                    "Int": {
                      "width": 64,
                      "signed": false
                    }
                  }
                ]
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 12,
                "col_start": 13,
                "line_end": 12,
                "col_end": 21
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 10,
                "projections": []
              },
              "rvalue": {
                "CheckedBinaryOp": [
                  "Add",
                  {
                    "Copy": {
                      "local": 2,
                      "projections": []
                    }
                  },
                  {
                    "Copy": {
                      "local": 9,
                      "projections": []
                    }
                  }
                ]
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 12,
                "col_start": 8,
                "line_end": 12,
                "col_end": 21
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 10,
                "projections": [
                  {
                    "Field": 1
                  }
                ]
              }
            },
            "expected": false,
            "msg": {
              "Overflow": "Add"
            },
            "target": 7,
            "span": {
              "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
              "line_start": 12,
              "col_start": 8,
              "line_end": 12,
              "col_end": 21
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 6,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 14,
                "col_start": 4,
                "line_end": 14,
                "col_end": 5
              }
            }
          }
        ],
        "terminator": "Return"
      },
      {
        "id": 7,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 2,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 10,
                    "projections": [
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "tests/trust-falsification/proved/wide_unsigned_accumulator.rs",
                "line_start": 12,
                "col_start": 8,
                "line_end": 12,
                "col_end": 21
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      }
    ],
    "arg_count": 1,
    "return_ty": {
      "Int": {
        "width": 64,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "Or": [
        {
          "Eq": [
            {
              "Var": [
                "_7",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Eq": [
            {
              "Var": [
                "_7",
                "Int"
              ]
            },
            {
              "Int": 1
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_MOD: &str = r##"{
  "name": "u_mod",
  "def_path": "uncond::u_mod",
  "span": {
    "file": "uncond.rs",
    "line_start": 5,
    "col_start": 0,
    "line_end": 8,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "a"
      },
      {
        "index": 3,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 4,
        "ty": "Bool",
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 6,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Eq",
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        0,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 6,
                "col_start": 8,
                "line_end": 6,
                "col_end": 13
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 4,
                "projections": []
              }
            },
            "expected": false,
            "msg": "RemainderByZero",
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 6,
              "col_start": 8,
              "line_end": 6,
              "col_end": 13
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Rem",
                  {
                    "Copy": {
                      "local": 2,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 6,
                "col_start": 4,
                "line_end": 6,
                "col_end": 13
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 7,
                "col_start": 8,
                "line_end": 7,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 5,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 7,
                "col_start": 4,
                "line_end": 7,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 6,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 2,
            "span": {
              "file": "uncond.rs",
              "line_start": 7,
              "col_start": 4,
              "line_end": 7,
              "col_end": 10
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": [
                      "Deref",
                      {
                        "Index": 5
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 7,
                "col_start": 4,
                "line_end": 7,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_MASK: &str = r##"{
  "name": "u_mask",
  "def_path": "uncond::u_mask",
  "span": {
    "file": "uncond.rs",
    "line_start": 9,
    "col_start": 0,
    "line_end": 12,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "a"
      },
      {
        "index": 3,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 4,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "BitAnd",
                  {
                    "Copy": {
                      "local": 2,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        3,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 10,
                "col_start": 4,
                "line_end": 10,
                "col_end": 13
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 11,
                "col_start": 8,
                "line_end": 11,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 4,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 11,
                "col_start": 4,
                "line_end": 11,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 5,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 11,
              "col_start": 4,
              "line_end": 11,
              "col_end": 10
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": [
                      "Deref",
                      {
                        "Index": 4
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 11,
                "col_start": 4,
                "line_end": 11,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_DIV: &str = r##"{
  "name": "u_div",
  "def_path": "uncond::u_div",
  "span": {
    "file": "uncond.rs",
    "line_start": 13,
    "col_start": 0,
    "line_end": 16,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 2,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 3,
        "ty": "Bool",
        "name": null
      },
      {
        "index": 4,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 3,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Eq",
                  {
                    "Constant": {
                      "Uint": [
                        2,
                        64
                      ]
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        0,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 14,
                "col_start": 8,
                "line_end": 14,
                "col_end": 13
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 3,
                "projections": []
              }
            },
            "expected": false,
            "msg": "DivisionByZero",
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 14,
              "col_start": 8,
              "line_end": 14,
              "col_end": 13
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Div",
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        2,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 14,
                "col_start": 4,
                "line_end": 14,
                "col_end": 13
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 15,
                "col_start": 8,
                "line_end": 15,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 4,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 15,
                "col_start": 4,
                "line_end": 15,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 5,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 2,
            "span": {
              "file": "uncond.rs",
              "line_start": 15,
              "col_start": 4,
              "line_end": 15,
              "col_end": 10
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": [
                      "Deref",
                      {
                        "Index": 4
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 15,
                "col_start": 4,
                "line_end": 15,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 2,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_CLAMPCAST: &str = r##"{
  "name": "u_clampcast",
  "def_path": "uncond::u_clampcast",
  "span": {
    "file": "uncond.rs",
    "line_start": 17,
    "col_start": 0,
    "line_end": 20,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 32,
            "signed": true
          }
        },
        "name": "a"
      },
      {
        "index": 3,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 4,
        "ty": {
          "Int": {
            "width": 32,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 6,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [],
        "terminator": {
          "Call": {
            "func": "<i32 as core::cmp::Ord>::clamp",
            "args": [
              {
                "Copy": {
                  "local": 2,
                  "projections": []
                }
              },
              {
                "Constant": {
                  "Int": 0
                }
              },
              {
                "Constant": {
                  "Int": 3
                }
              }
            ],
            "dest": {
              "local": 4,
              "projections": []
            },
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 18,
              "col_start": 8,
              "line_end": 18,
              "col_end": 21
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Cast": [
                  {
                    "Move": {
                      "local": 4,
                      "projections": []
                    }
                  },
                  {
                    "Int": {
                      "width": 64,
                      "signed": false
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 18,
                "col_start": 4,
                "line_end": 18,
                "col_end": 30
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 19,
                "col_start": 8,
                "line_end": 19,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 5,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 19,
                "col_start": 4,
                "line_end": 19,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 6,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 2,
            "span": {
              "file": "uncond.rs",
              "line_start": 19,
              "col_start": 4,
              "line_end": 19,
              "col_end": 10
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": [
                      "Deref",
                      {
                        "Index": 5
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 19,
                "col_start": 4,
                "line_end": 19,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": -2147483648
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "a",
                "Int"
              ]
            },
            {
              "Int": 2147483647
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_ENUMTAG: &str = r##"{
  "name": "u_enumtag",
  "def_path": "uncond::u_enumtag",
  "span": {
    "file": "uncond.rs",
    "line_start": 21,
    "col_start": 0,
    "line_end": 24,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "k"
      },
      {
        "index": 2,
        "ty": {
          "Adt": {
            "name": "uncond::E",
            "fields": [
              [
                "__tag",
                {
                  "Int": {
                    "width": 64,
                    "signed": true
                  }
                }
              ]
            ],
            "variants": [
              {
                "name": "A",
                "discriminant": 0,
                "fields": []
              },
              {
                "name": "B",
                "discriminant": 1,
                "fields": []
              }
            ],
            "disc_index_safe": true,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Enum"
          }
        },
        "name": "e"
      },
      {
        "index": 3,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 4,
        "ty": {
          "Int": {
            "width": 64,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 6,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "Discriminant": {
                  "local": 2,
                  "projections": []
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 22,
                "col_start": 8,
                "line_end": 22,
                "col_end": 18
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Cast": [
                  {
                    "Move": {
                      "local": 4,
                      "projections": []
                    }
                  },
                  {
                    "Int": {
                      "width": 64,
                      "signed": false
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 22,
                "col_start": 4,
                "line_end": 22,
                "col_end": 18
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 23,
                "col_start": 8,
                "line_end": 23,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 5,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 23,
                "col_start": 4,
                "line_end": 23,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 6,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 23,
              "col_start": 4,
              "line_end": 23,
              "col_end": 10
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": [
                      "Deref",
                      {
                        "Index": 5
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 23,
                "col_start": 4,
                "line_end": 23,
                "col_end": 10
              }
            }
          }
        ],
        "terminator": "Return"
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "Or": [
        {
          "Eq": [
            {
              "Var": [
                "_4",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Eq": [
            {
              "Var": [
                "_4",
                "Int"
              ]
            },
            {
              "Int": 1
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "k",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_FLAT: &str = r##"{
  "name": "u_flat",
  "def_path": "uncond::u_flat",
  "span": {
    "file": "uncond.rs",
    "line_start": 37,
    "col_start": 0,
    "line_end": 46,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "i"
      },
      {
        "index": 2,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 6
              }
            }
          }
        },
        "name": "g"
      },
      {
        "index": 3,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": "s"
      },
      {
        "index": 4,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 6,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": "iter"
      },
      {
        "index": 7,
        "ty": {
          "Adt": {
            "name": "core::option::Option",
            "fields": [
              [
                "__tag",
                {
                  "Int": {
                    "width": 64,
                    "signed": true
                  }
                }
              ],
              [
                "__v1_0",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [
              {
                "name": "None",
                "discriminant": 0,
                "fields": []
              },
              {
                "name": "Some",
                "discriminant": 1,
                "fields": [
                  [
                    "0",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ]
                ]
              }
            ],
            "disc_index_safe": true,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Enum"
          }
        },
        "name": null
      },
      {
        "index": 8,
        "ty": {
          "Ref": {
            "mutable": true,
            "inner": {
              "Adt": {
                "name": "core::ops::range::Range",
                "fields": [
                  [
                    "start",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ],
                  [
                    "end",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ]
                ],
                "variants": [],
                "disc_index_safe": false,
                "faithful_enum_repr": null,
                "layout": null,
                "enum_layout": null,
                "adt_kind": "Struct"
              }
            }
          }
        },
        "name": null
      },
      {
        "index": 9,
        "ty": {
          "Int": {
            "width": 64,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 10,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "y"
      },
      {
        "index": 11,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 12,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": null
      },
      {
        "index": 13,
        "ty": {
          "Adt": {
            "name": "core::ops::range::Range",
            "fields": [
              [
                "start",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ],
              [
                "end",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [],
            "disc_index_safe": false,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Struct"
          }
        },
        "name": "iter"
      },
      {
        "index": 14,
        "ty": {
          "Adt": {
            "name": "core::option::Option",
            "fields": [
              [
                "__tag",
                {
                  "Int": {
                    "width": 64,
                    "signed": true
                  }
                }
              ],
              [
                "__v1_0",
                {
                  "Int": {
                    "width": 64,
                    "signed": false
                  }
                }
              ]
            ],
            "variants": [
              {
                "name": "None",
                "discriminant": 0,
                "fields": []
              },
              {
                "name": "Some",
                "discriminant": 1,
                "fields": [
                  [
                    "0",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ]
                ]
              }
            ],
            "disc_index_safe": true,
            "faithful_enum_repr": null,
            "layout": null,
            "enum_layout": null,
            "adt_kind": "Enum"
          }
        },
        "name": null
      },
      {
        "index": 15,
        "ty": {
          "Ref": {
            "mutable": true,
            "inner": {
              "Adt": {
                "name": "core::ops::range::Range",
                "fields": [
                  [
                    "start",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ],
                  [
                    "end",
                    {
                      "Int": {
                        "width": 64,
                        "signed": false
                      }
                    }
                  ]
                ],
                "variants": [],
                "disc_index_safe": false,
                "faithful_enum_repr": null,
                "layout": null,
                "enum_layout": null,
                "adt_kind": "Struct"
              }
            }
          }
        },
        "name": null
      },
      {
        "index": 16,
        "ty": {
          "Int": {
            "width": 64,
            "signed": true
          }
        },
        "name": null
      },
      {
        "index": 17,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "x"
      },
      {
        "index": 18,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 19,
        "ty": {
          "Tuple": [
            {
              "Int": {
                "width": 64,
                "signed": false
              }
            },
            "Bool"
          ]
        },
        "name": null
      },
      {
        "index": 20,
        "ty": {
          "Tuple": [
            {
              "Int": {
                "width": 64,
                "signed": false
              }
            },
            "Bool"
          ]
        },
        "name": null
      },
      {
        "index": 21,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 22,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 23,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 24,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 25,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 3,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      0,
                      8
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 38,
                "col_start": 16,
                "line_end": 38,
                "col_end": 19
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "Aggregate": [
                  {
                    "Adt": {
                      "name": "core::ops::range::Range",
                      "variant": 0,
                      "active_field": null,
                      "args": "core::ops::range::Range<usize>"
                    }
                  },
                  [
                    {
                      "Constant": {
                        "Uint": [
                          0,
                          64
                        ]
                      }
                    },
                    {
                      "Constant": {
                        "Uint": [
                          2,
                          64
                        ]
                      }
                    }
                  ]
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 39,
                "col_start": 13,
                "line_end": 39,
                "col_end": 22
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::ops::range::Range<usize> as core::iter::traits::collect::IntoIterator>::into_iter",
            "args": [
              {
                "Move": {
                  "local": 5,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 4,
              "projections": []
            },
            "target": 1,
            "span": {
              "file": "uncond.rs",
              "line_start": 39,
              "col_start": 13,
              "line_end": 39,
              "col_end": 22
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 4,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 39,
                "col_start": 13,
                "line_end": 39,
                "col_end": 22
              }
            }
          }
        ],
        "terminator": {
          "Goto": 2
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 8,
                "projections": []
              },
              "rvalue": {
                "Ref": {
                  "mutable": true,
                  "place": {
                    "local": 6,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 39,
                "col_start": 13,
                "line_end": 39,
                "col_end": 22
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next",
            "args": [
              {
                "Copy": {
                  "local": 8,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 7,
              "projections": []
            },
            "target": 3,
            "span": {
              "file": "uncond.rs",
              "line_start": 39,
              "col_start": 13,
              "line_end": 39,
              "col_end": 22
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 9,
                "projections": []
              },
              "rvalue": {
                "Discriminant": {
                  "local": 7,
                  "projections": []
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 39,
                "col_start": 13,
                "line_end": 39,
                "col_end": 22
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 9,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                6
              ],
              [
                1,
                5
              ]
            ],
            "otherwise": 4,
            "exhaustive_enum_unreachable": true,
            "span": {
              "file": "uncond.rs",
              "line_start": 39,
              "col_start": 13,
              "line_end": 39,
              "col_end": 22
            }
          }
        }
      },
      {
        "id": 4,
        "stmts": [],
        "terminator": "Unreachable"
      },
      {
        "id": 5,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 10,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 7,
                    "projections": [
                      {
                        "Downcast": 1
                      },
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 39,
                "col_start": 8,
                "line_end": 39,
                "col_end": 9
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 12,
                "projections": []
              },
              "rvalue": {
                "Aggregate": [
                  {
                    "Adt": {
                      "name": "core::ops::range::Range",
                      "variant": 0,
                      "active_field": null,
                      "args": "core::ops::range::Range<usize>"
                    }
                  },
                  [
                    {
                      "Constant": {
                        "Uint": [
                          0,
                          64
                        ]
                      }
                    },
                    {
                      "Constant": {
                        "Uint": [
                          3,
                          64
                        ]
                      }
                    }
                  ]
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 40,
                "col_start": 17,
                "line_end": 40,
                "col_end": 26
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::ops::range::Range<usize> as core::iter::traits::collect::IntoIterator>::into_iter",
            "args": [
              {
                "Move": {
                  "local": 12,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 11,
              "projections": []
            },
            "target": 7,
            "span": {
              "file": "uncond.rs",
              "line_start": 40,
              "col_start": 17,
              "line_end": 40,
              "col_end": 26
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 6,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 45,
                "col_start": 4,
                "line_end": 45,
                "col_end": 5
              }
            }
          }
        ],
        "terminator": "Return"
      },
      {
        "id": 7,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 13,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 11,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 40,
                "col_start": 17,
                "line_end": 40,
                "col_end": 26
              }
            }
          }
        ],
        "terminator": {
          "Goto": 8
        }
      },
      {
        "id": 8,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 15,
                "projections": []
              },
              "rvalue": {
                "Ref": {
                  "mutable": true,
                  "place": {
                    "local": 13,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 40,
                "col_start": 17,
                "line_end": 40,
                "col_end": 26
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "<core::ops::range::Range<usize> as core::iter::traits::iterator::Iterator>::next",
            "args": [
              {
                "Copy": {
                  "local": 15,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 14,
              "projections": []
            },
            "target": 9,
            "span": {
              "file": "uncond.rs",
              "line_start": 40,
              "col_start": 17,
              "line_end": 40,
              "col_end": 26
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 9,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 16,
                "projections": []
              },
              "rvalue": {
                "Discriminant": {
                  "local": 14,
                  "projections": []
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 40,
                "col_start": 17,
                "line_end": 40,
                "col_end": 26
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 16,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                2
              ],
              [
                1,
                10
              ]
            ],
            "otherwise": 4,
            "exhaustive_enum_unreachable": true,
            "span": {
              "file": "uncond.rs",
              "line_start": 40,
              "col_start": 17,
              "line_end": 40,
              "col_end": 26
            }
          }
        }
      },
      {
        "id": 10,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 17,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 14,
                    "projections": [
                      {
                        "Downcast": 1
                      },
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 40,
                "col_start": 12,
                "line_end": 40,
                "col_end": 13
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 19,
                "projections": []
              },
              "rvalue": {
                "CheckedBinaryOp": [
                  "Mul",
                  {
                    "Copy": {
                      "local": 10,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        3,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 41,
                "col_start": 16,
                "line_end": 41,
                "col_end": 21
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 19,
                "projections": [
                  {
                    "Field": 1
                  }
                ]
              }
            },
            "expected": false,
            "msg": {
              "Overflow": "Mul"
            },
            "target": 11,
            "span": {
              "file": "uncond.rs",
              "line_start": 41,
              "col_start": 16,
              "line_end": 41,
              "col_end": 21
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 11,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 18,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 19,
                    "projections": [
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 41,
                "col_start": 16,
                "line_end": 41,
                "col_end": 21
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 20,
                "projections": []
              },
              "rvalue": {
                "CheckedBinaryOp": [
                  "Add",
                  {
                    "Copy": {
                      "local": 18,
                      "projections": []
                    }
                  },
                  {
                    "Copy": {
                      "local": 17,
                      "projections": []
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 41,
                "col_start": 16,
                "line_end": 41,
                "col_end": 25
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 20,
                "projections": [
                  {
                    "Field": 1
                  }
                ]
              }
            },
            "expected": false,
            "msg": {
              "Overflow": "Add"
            },
            "target": 12,
            "span": {
              "file": "uncond.rs",
              "line_start": 41,
              "col_start": 16,
              "line_end": 41,
              "col_end": 25
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 12,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 20,
                    "projections": [
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 41,
                "col_start": 12,
                "line_end": 41,
                "col_end": 25
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 22,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 42,
                "col_start": 16,
                "line_end": 42,
                "col_end": 17
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 24,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 42,
                "col_start": 33,
                "line_end": 42,
                "col_end": 34
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 25,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 24,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        6,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 42,
                "col_start": 31,
                "line_end": 42,
                "col_end": 35
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 25,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 13,
            "span": {
              "file": "uncond.rs",
              "line_start": 42,
              "col_start": 31,
              "line_end": 42,
              "col_end": 35
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 13,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 23,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 2,
                    "projections": [
                      "Deref",
                      {
                        "Index": 24
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 42,
                "col_start": 31,
                "line_end": 42,
                "col_end": 35
              }
            }
          }
        ],
        "terminator": {
          "Call": {
            "func": "@trust-rustc-total-primitive-method::core::num::<impl u8>::wrapping_add",
            "args": [
              {
                "Move": {
                  "local": 22,
                  "projections": []
                }
              },
              {
                "Move": {
                  "local": 23,
                  "projections": []
                }
              }
            ],
            "dest": {
              "local": 21,
              "projections": []
            },
            "target": 14,
            "span": {
              "file": "uncond.rs",
              "line_start": 42,
              "col_start": 16,
              "line_end": 42,
              "col_end": 36
            },
            "atomic": null,
            "is_foreign": false,
            "is_unsafe_sig": false,
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 14,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 3,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 21,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 42,
                "col_start": 12,
                "line_end": 42,
                "col_end": 36
              }
            }
          }
        ],
        "terminator": {
          "Goto": 8
        }
      }
    ],
    "arg_count": 2,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "Or": [
        {
          "Eq": [
            {
              "Var": [
                "_9",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Eq": [
            {
              "Var": [
                "_9",
                "Int"
              ]
            },
            {
              "Int": 1
            }
          ]
        }
      ]
    },
    {
      "Or": [
        {
          "Eq": [
            {
              "Var": [
                "_16",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Eq": [
            {
              "Var": [
                "_16",
                "Int"
              ]
            },
            {
              "Int": 1
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "i",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "i",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

const MIR_U_CHECKEDSUB: &str = r##"{
  "name": "u_checkedsub",
  "def_path": "uncond::u_checkedsub",
  "span": {
    "file": "uncond.rs",
    "line_start": 29,
    "col_start": 0,
    "line_end": 36,
    "col_end": 1
  },
  "body": {
    "locals": [
      {
        "index": 0,
        "ty": {
          "Int": {
            "width": 8,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 1,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "hi"
      },
      {
        "index": 2,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": "n"
      },
      {
        "index": 3,
        "ty": {
          "Ref": {
            "mutable": false,
            "inner": {
              "Array": {
                "elem": {
                  "Int": {
                    "width": 8,
                    "signed": false
                  }
                },
                "len": 4
              }
            }
          }
        },
        "name": "arr"
      },
      {
        "index": 4,
        "ty": "Bool",
        "name": null
      },
      {
        "index": 5,
        "ty": {
          "Tuple": [
            {
              "Int": {
                "width": 64,
                "signed": false
              }
            },
            "Bool"
          ]
        },
        "name": null
      },
      {
        "index": 6,
        "ty": {
          "Int": {
            "width": 64,
            "signed": false
          }
        },
        "name": null
      },
      {
        "index": 7,
        "ty": "Bool",
        "name": null
      }
    ],
    "blocks": [
      {
        "id": 0,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 4,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Le",
                  {
                    "Copy": {
                      "local": 2,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        3,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 30,
                "col_start": 7,
                "line_end": 30,
                "col_end": 13
              }
            }
          }
        ],
        "terminator": {
          "SwitchInt": {
            "discr": {
              "Move": {
                "local": 4,
                "projections": []
              }
            },
            "targets": [
              [
                0,
                4
              ]
            ],
            "otherwise": 1,
            "exhaustive_enum_unreachable": false,
            "span": {
              "file": "uncond.rs",
              "line_start": 30,
              "col_start": 7,
              "line_end": 30,
              "col_end": 13
            }
          }
        }
      },
      {
        "id": 1,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 5,
                "projections": []
              },
              "rvalue": {
                "CheckedBinaryOp": [
                  "Sub",
                  {
                    "Constant": {
                      "Uint": [
                        3,
                        64
                      ]
                    }
                  },
                  {
                    "Copy": {
                      "local": 2,
                      "projections": []
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 31,
                "col_start": 13,
                "line_end": 31,
                "col_end": 18
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 5,
                "projections": [
                  {
                    "Field": 1
                  }
                ]
              }
            },
            "expected": false,
            "msg": {
              "Overflow": "Sub"
            },
            "target": 2,
            "span": {
              "file": "uncond.rs",
              "line_start": 31,
              "col_start": 13,
              "line_end": 31,
              "col_end": 18
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 2,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 1,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Move": {
                    "local": 5,
                    "projections": [
                      {
                        "Field": 0
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 31,
                "col_start": 8,
                "line_end": 31,
                "col_end": 18
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 6,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 1,
                    "projections": []
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 32,
                "col_start": 12,
                "line_end": 32,
                "col_end": 14
              }
            }
          },
          {
            "Assign": {
              "place": {
                "local": 7,
                "projections": []
              },
              "rvalue": {
                "BinaryOp": [
                  "Lt",
                  {
                    "Copy": {
                      "local": 6,
                      "projections": []
                    }
                  },
                  {
                    "Constant": {
                      "Uint": [
                        4,
                        64
                      ]
                    }
                  }
                ]
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 32,
                "col_start": 8,
                "line_end": 32,
                "col_end": 15
              }
            }
          }
        ],
        "terminator": {
          "Assert": {
            "cond": {
              "Move": {
                "local": 7,
                "projections": []
              }
            },
            "expected": true,
            "msg": "BoundsCheck",
            "target": 3,
            "span": {
              "file": "uncond.rs",
              "line_start": 32,
              "col_start": 8,
              "line_end": 32,
              "col_end": 15
            },
            "unwind": "Continue"
          }
        }
      },
      {
        "id": 3,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Copy": {
                    "local": 3,
                    "projections": [
                      "Deref",
                      {
                        "Index": 6
                      }
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 32,
                "col_start": 8,
                "line_end": 32,
                "col_end": 15
              }
            }
          }
        ],
        "terminator": {
          "Goto": 5
        }
      },
      {
        "id": 4,
        "stmts": [
          {
            "Assign": {
              "place": {
                "local": 0,
                "projections": []
              },
              "rvalue": {
                "Use": {
                  "Constant": {
                    "Uint": [
                      0,
                      8
                    ]
                  }
                }
              },
              "span": {
                "file": "uncond.rs",
                "line_start": 34,
                "col_start": 8,
                "line_end": 34,
                "col_end": 9
              }
            }
          }
        ],
        "terminator": {
          "Goto": 5
        }
      },
      {
        "id": 5,
        "stmts": [],
        "terminator": "Return"
      }
    ],
    "arg_count": 3,
    "return_ty": {
      "Int": {
        "width": 8,
        "signed": false
      }
    }
  },
  "contracts": [],
  "preconditions": [
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "hi",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "hi",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    },
    {
      "And": [
        {
          "Ge": [
            {
              "Var": [
                "n",
                "Int"
              ]
            },
            {
              "Int": 0
            }
          ]
        },
        {
          "Le": [
            {
              "Var": [
                "n",
                "Int"
              ]
            },
            {
              "Int": 18446744073709551615
            }
          ]
        }
      ]
    }
  ],
  "postconditions": [],
  "spec": {
    "requires": [],
    "ensures": [],
    "invariants": []
  }
}"##;

/// R2 — THE WITNESS THAT REMOVED THE LIVENESS RELAXATION. `-Ztrust-dump=mir` capture,
/// PRISTINE 70a7534fd1 stage2, of
///
/// ```ignore
/// #[core::contracts::requires(k >= 10)]
/// pub fn deadentry_pre(mut k: usize, a: usize, y: usize, arr: &[u8;4], b: &[u8;4]) -> u8 {
///     let t = b[y];
///     k = a & 3;
///     arr[k] | t
/// }
/// ```
///
/// Nothing in `body.blocks` reads `k` before the store, so a liveness analysis of the
/// blocks called its ENTRY value dead. `vc.formula` ALSO carries the function's
/// PRECONDITIONS, and `requires(k >= 10)` speaks about that entry value: the bitmask
/// fact `k <= 3` renamed onto the same symbol contradicts it, the path goes UNSAT, and
/// `b[y]` — a genuine out-of-bounds read for every `y >= 4` — is proved VACUOUSLY.
const MIR_DEADENTRY_PRE: &str = r##"{"name":"deadentry_pre","def_path":"pre1::deadentry_pre","span":{"file":"pre1.rs","line_start":5,"col_start":0,"line_end":9,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"k"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"a"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"y"},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"arr"},{"index":5,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"b"},{"index":6,"ty":{"Closure":{"name":"pre1::deadentry_pre::{closure#0}","upvars":[{"Ref":{"mutable":false,"inner":{"Int":{"width":64,"signed":false}}}}],"call":{"kind":"Fn","params":[],"ret":"Bool"}}},"name":null},{"index":7,"ty":{"Int":{"width":8,"signed":false}},"name":"t"},{"index":8,"ty":"Bool","name":null},{"index":9,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":10,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":11,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"pre1.rs","line_start":6,"col_start":12,"line_end":6,"col_end":16}}}],"terminator":{"Assert":{"cond":{"Move":{"local":8,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":1,"span":{"file":"pre1.rs","line_start":6,"col_start":12,"line_end":6,"col_end":16},"unwind":"Continue"}}},{"id":1,"stmts":[{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Use":{"Copy":{"local":5,"projections":["Deref",{"Index":3}]}}},"span":{"file":"pre1.rs","line_start":6,"col_start":12,"line_end":6,"col_end":16}}},{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"BinaryOp":["BitAnd",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[3,64]}}]},"span":{"file":"pre1.rs","line_start":7,"col_start":4,"line_end":7,"col_end":13}}},{"Assign":{"place":{"local":10,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"pre1.rs","line_start":8,"col_start":8,"line_end":8,"col_end":9}}},{"Assign":{"place":{"local":11,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":10,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"pre1.rs","line_start":8,"col_start":4,"line_end":8,"col_end":10}}}],"terminator":{"Assert":{"cond":{"Move":{"local":11,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":2,"span":{"file":"pre1.rs","line_start":8,"col_start":4,"line_end":8,"col_end":10},"unwind":"Continue"}}},{"id":2,"stmts":[{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":["Deref",{"Index":10}]}}},"span":{"file":"pre1.rs","line_start":8,"col_start":4,"line_end":8,"col_end":10}}},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"BinaryOp":["BitOr",{"Move":{"local":9,"projections":[]}},{"Copy":{"local":7,"projections":[]}}]},"span":{"file":"pre1.rs","line_start":8,"col_start":4,"line_end":8,"col_end":14}}}],"terminator":"Return"}],"arg_count":5,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[{"kind":"Requires","span":{"file":"pre1.rs","line_start":4,"col_start":28,"line_end":4,"col_end":35},"body":"__trust_lowered_compiler_contract__:(k) >= (10)"}],"preconditions":[{"Ge":[{"Var":["k","Int"]},{"Int":10}]},{"And":[{"Ge":[{"Var":["k","Int"]},{"Int":0}]},{"Le":[{"Var":["k","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["a","Int"]},{"Int":0}]},{"Le":[{"Var":["a","Int"]},{"Int":18446744073709551615}]}]},{"And":[{"Ge":[{"Var":["y","Int"]},{"Int":0}]},{"Le":[{"Var":["y","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":["(k) >= (10)"],"ensures":[],"invariants":[]}}"##;

/// One `(kind, verdict, kernel-certified)` row per VC, from the REAL in-process ay
/// backend, on a big stack (VC generation and the solver search both overflow
/// libtest's default stack).
/// Like [`verdicts`], but keeps each row's source LINE, so two rows of the SAME
/// `VcKind` can be told apart.
///
/// `deadentry_pre` emits two `IndexOutOfBounds` rows: `b[y]` at line 6, which is a
/// genuine out-of-bounds read for every `y >= 4`, and `arr[k]` at line 8, where
/// `k = a & 3` on a `[u8;4]` is provably in range. A guard that ranges over BOTH
/// cannot say which one it is about, and once `ay` learned constant-index/bitmask
/// reasoning the harmless row began to prove and took the guard down with it.
fn verdicts_with_line(mir: &str) -> Vec<(VcKind, u32, VerificationResult, bool)> {
    let func: VerifiableFunction =
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    let line = vc.location.line_start;
                    (vc.kind, line, r, certified)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The named row must REFUTE with a counterexample, and must not be certified.
///
/// STRICTER than asserting "no row of this kind proves": it names WHICH row the
/// guard is about, so a sibling row becoming provable — a solver getting better at
/// a genuinely safe index — can never silently disarm it.
fn assert_row_at_line_refutes(mir: &str, want: fn(&VcKind) -> bool, line: u32, what: &str) {
    let all = verdicts_with_line(mir);
    let rows: Vec<_> = all.iter().filter(|(k, l, _, _)| want(k) && *l == line).collect();
    assert!(!rows.is_empty(), "{what}: no row of that kind at line {line}; got {all:?}");
    assert!(
        rows.iter().all(|(_, _, r, _)| !is_proved(r)),
        "{what}: the vacuous row at line {line} is PROVED again; got {rows:?}"
    );
    assert!(
        rows.iter().any(|(_, _, r, _)| matches!(
            r,
            VerificationResult::Failed { counterexample: Some(_), .. }
        )),
        "{what}: the row at line {line} must be REFUTED with a counterexample, not merely \
         undecided; got {rows:?}"
    );
    assert!(
        rows.iter()
            .filter(|(_, _, r, _)| matches!(r, VerificationResult::Failed { .. }))
            .all(|(_, _, _, c)| !*c),
        "{what}: a REFUTED row may not also be kernel-certified; got {rows:?}"
    );
}

fn verdicts(mir: &str) -> Vec<(VcKind, VerificationResult, bool)> {
    let func: VerifiableFunction =
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc.kind, r, certified)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn rows_of(mir: &str, want: fn(&VcKind) -> bool) -> Vec<(VerificationResult, bool)> {
    let rows: Vec<_> = verdicts(mir)
        .into_iter()
        .filter(|(kind, _, _)| want(kind))
        .map(|(_, r, c)| (r, c))
        .collect();
    assert!(!rows.is_empty(), "the obligation this row is about must be generated at all");
    rows
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

fn is_add_overflow(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: trust_types::BinOp::Add, .. })
}

/// The vacuous row must carry a real COUNTEREXAMPLE (`Failed`), not merely go
/// `Unknown`: "the solver gave up" would satisfy a `!is_proved` assert without showing
/// the gate closed anything. A REFUTED row may never also be kernel-certified.
fn assert_refutes(mir: &str, want: fn(&VcKind) -> bool, what: &str) {
    let rows = rows_of(mir, want);
    assert!(
        rows.iter().all(|(r, _)| !is_proved(r)),
        "{what}: the vacuous row is PROVED again; got {rows:?}"
    );
    assert!(
        rows.iter()
            .any(|(r, _)| matches!(r, VerificationResult::Failed { counterexample: Some(_), .. })),
        "{what}: the vacuous row must be REFUTED with a counterexample, not merely \
         undecided; got {rows:?}"
    );
    assert!(
        rows.iter()
            .filter(|(r, _)| matches!(r, VerificationResult::Failed { .. }))
            .all(|(_, c)| !c),
        "{what}: a REFUTED row may not also be kernel-certified; got {rows:?}"
    );
}

/// The honest DECLINE: nothing proves and nothing carries a counterexample. Distinct
/// from [`assert_false_refutation`] on purpose — the two are different prices.
///
/// No row pays this price since 2026-11-07 (`u_mod` was the last, and was promoted);
/// it stays for the next decline this file records.
#[allow(dead_code)]
fn assert_undecided(mir: &str, want: fn(&VcKind) -> bool, what: &str) {
    let rows = rows_of(mir, want);
    assert!(rows.iter().all(|(r, _)| !is_proved(r)), "{what}: still proves; got {rows:?}");
    assert!(
        rows.iter().all(|(r, _)| !matches!(r, VerificationResult::Failed { .. })),
        "{what}: this row is recorded as a DECLINE; a refutation of a program the \
         runtime oracle never panics on is a different (worse) price and must be \
         re-adjudicated here rather than absorbed. Got {rows:?}"
    );
}

/// A REFUTATION of a program the runtime oracle never panics on. The counterexample is
/// spurious — it names a value of the parameter's ENTRY version that no execution
/// reads. Recorded so that recovering the proof shows up as a failure to promote.
///
/// No row pays this price since 2026-09-29 (`u_flat` was the last, and was promoted);
/// it stays for the next false refutation this file records.
#[allow(dead_code)]
fn assert_false_refutation(mir: &str, want: fn(&VcKind) -> bool, what: &str) {
    let rows = rows_of(mir, want);
    assert!(rows.iter().all(|(r, _)| !is_proved(r)), "{what}: still proves; got {rows:?}");
    assert!(
        rows.iter()
            .any(|(r, _)| matches!(r, VerificationResult::Failed { counterexample: Some(_), .. })),
        "{what}: recorded as a FALSE REFUTATION; got {rows:?}"
    );
    assert!(
        rows.iter()
            .filter(|(r, _)| matches!(r, VerificationResult::Failed { .. }))
            .all(|(_, c)| !c),
        "{what}: a REFUTED row may not also be kernel-certified; got {rows:?}"
    );
}

fn assert_all_proved_and_certified(mir: &str, what: &str) {
    for (kind, verdict, certified) in verdicts(mir) {
        assert!(
            is_proved(&verdict) && certified,
            "{what}: {kind:?} got {verdict:?} certified={certified}"
        );
    }
}

// ── W1: THE DEF RESOLVER, not the counter ──────────────────────────────────
//
// `local_defs::unique_value_def` (was `crate::unique_whole_local_def`) counted
// whole-local `Statement::Assign` places only and handed a once-reassigned PARAMETER
// back as if that store were the parameter's universal value. `stable_min_arg_formula`
// (`generate/callee_summaries.rs`) resolves through it for FOUR producers —
// `build_modulo_bound_facts`, `build_division_lt_facts`, `build_division_exact_facts`,
// `build_min_max_facts` — and INLINES the result as a constant into a fact keyed on
// the parameter's bare name, so version-renaming cannot rescue it. Both rows below are
// killed by mutant W1-REVERT (dropping the entry-definition check at the end of
// `unique_value_def`), under which each returns to `Proved` + kernel-certified.

/// `-Ztrust-dump` capture of
///
///   pub fn param_mod_divisor_guarded(a: usize, mut m: usize, c: bool, arr: &[u8;4]) -> u8 {
///       if c { m = 4; } if m == 0 { return 0; } let k = a % m; arr[k] }
///
/// The divisor `m` resolves to the constant `4`, so `build_modulo_bound_facts` emits
/// `(4 == 0) ∨ (k < 4)` — false on the `c == false` edge, where `m` is the argument.
/// PRISTINE 70a7534fd1 stage2, `-Ztrust-policy=certify`: rc=0, "3 proved, 0 failed,
/// 0 unknown, 0 timed out, 0 runtime-checked out of 3 obligation(s)", "of which 3
/// kernel-certified by the clean CIC kernel". Runtime oracle (stock rustc, `-O -C
/// debug-assertions=on`, `#[inline(never)]`, `black_box`, `catch_unwind`): 6 of 128
/// panic over a in 0..8 x m in 0..8 x c in {false,true}; first (a=4, m=5, c=false).
#[test]
fn param_modulo_divisor_operand_still_refutes() {
    assert_refutes(MIR_PARAM_MOD_DIVISOR_GUARDED, is_bounds, "param_mod_divisor_guarded");
}

/// `-Ztrust-dump` capture of
///
///   pub fn param_min_arg(a: usize, mut b: usize, c: bool, arr: &[u8;4]) -> u8 {
///       if c { b = 3; } let n = a.min(b); arr[n] }
///
/// The `Ord::min` argument `b` resolves to the constant `3`, so `build_min_max_facts`
/// emits `n <= 3` — false on the `c == false` edge.
/// PRISTINE stage2: rc=0, "1 proved, 0 failed, 0 unknown, 0 timed out, 0
/// runtime-checked out of 1 obligation(s)", "of which 1 kernel-certified".
/// Runtime oracle: 16 of 128 panic over a in 0..8 x b in 0..8 x c in {false,true};
/// first (a=4, b=4, c=false).
#[test]
fn param_min_argument_still_refutes() {
    assert_refutes(MIR_PARAM_MIN_ARG, is_bounds, "param_min_arg");
}

// ── W2: a producer missing from the census ─────────────────────────────────

/// `-Ztrust-dump` capture of
///
///   pub fn u64_acc_param(mut t: u64, a: &[u8;64], c: bool) -> u64 {
///       if c { t = 0; } for &x in a { t += x as u64; } t }
///
/// `build_accumulator_bound_facts` (`generate/loop_bounds.rs`) gated on
/// `accumulator_init_const`, whose `def_count == 2 && saw_self_add` accepted "const
/// init + self-add" without asking whether the accumulator is a PARAMETER. Its three
/// values — the argument, the `0`, and the self-add result — read as two, and
/// `t <= 0 + 64*255` was emitted on the bare parameter name.
/// PRISTINE stage2: rc=0, "2 proved, 0 failed, 0 unknown, 0 timed out, 0
/// runtime-checked out of 2 obligation(s)", "of which 2 kernel-certified".
/// Runtime oracle: 6 of 48 panic over t in {0, 2^63, u64::MAX, MAX-255, MAX-16320,
/// MAX-16319} x every-element in {0,1,128,255} x c in {false,true}; first
/// (t=u64::MAX, elem=1, c=false).
///
/// THE FIX HERE IS UPSTREAM'S, not this lane's. `accumulator_init_const` stays the raw
/// recognizer for the BMC lane, and every lane that ASSERTS the bound goes through
/// `accumulator_bound_init_const`, which refuses a parameter accumulator outright.
/// Deleting that wrapper's parameter bail returns this row to `Proved`.
#[test]
fn param_accumulator_bound_still_refutes() {
    assert_refutes(MIR_U64_ACC_PARAM, is_add_overflow, "u64_acc_param");
}

/// W2's CONTROL: the same accumulator with a body-local `t`. Its two values ARE the
/// const init and the self-add, so the accumulator budget is untouched by W2 —
/// `param_accumulator_bound_still_refutes`'s tightening does NOT reach this row, and
/// dropping W2 must not make it prove for the wrong reason. It is captured from
/// `tests/trust-falsification/proved/wide_unsigned_accumulator.rs`, whose runtime
/// oracle never panics, so it must stay PROVED and kernel-certified.
///
/// It stands on a bound the seam's open ESCAPE defect supplies: `for &x in a` desugars
/// to `_7 = &mut _iter; Iterator::next(_7)`, so the slice-length / yield bound behind
/// `t <= 64*255` is resolved only because `local_defs::unique_value_def` still admits
/// an aliased local. Refusing the alias there turns this row into a FALSE REFUTATION
/// of a correct program — see `body_unique_value_def`'s `Escape` arm for why the
/// repair is an origin question and not that refusal.
#[test]
fn the_non_parameter_accumulator_still_proves() {
    assert_all_proved_and_certified(MIR_U64_ACC, "wide_unsigned_accumulator::u64_acc");
}

// ── THE WITNESS THAT REMOVED THE LIVENESS RELAXATION ───────────────────────

/// PRISTINE stage2, `-Ztrust-policy=certify`: rc=0, "3 proved, 0 failed, 0 unknown,
/// 0 timed out, 0 runtime-checked out of 3", "of which 2 kernel-certified". Both
/// `IndexOutOfBounds` rows were `Proved` AND kernel-certified at the vcgen+ay layer
/// while the relaxation stood.
///
/// Runtime oracle (stock rustc, `-O -C debug-assertions=on`, `#[inline(never)]`,
/// `black_box`, `catch_unwind`): 128/256 panicked over
/// `k in {10, 11, 20, usize::MAX} x a in 0..8 x y in 0..8` — every `y >= 4` reads
/// `b[y]` out of a `[u8; 4]`. `k >= 10` is the whole `requires` domain, so every one
/// of those inputs is a legal call.
#[test]
fn a_requires_contract_on_a_stored_parameter_still_refutes() {
    // Line 6 is `let t = b[y]` — out of bounds for every `y >= 4`, and `requires(k >= 10)`
    // admits all of them (the runtime oracle panicked 128/256). THAT is the row this
    // guard exists for, and it still refutes with the witness `y = 4`.
    //
    // RE-AIMED 2026-09-13. It used to assert that NO `is_bounds` row proves, which also
    // covered `arr[k]` at line 8 — where `k = a & 3` on a `[u8;4]` is provably in range.
    // When main advanced `ay` by 43 commits (constant-index/bitmask reasoning) that
    // harmless row began to prove, correctly, and failed this test. Naming the row makes
    // the guard STRICTER, not weaker: a sibling becoming provable can no longer disarm it,
    // and a regression on `b[y]` is still caught. Verified pre-existing by A/B against the
    // merge base, so this is main's to re-aim, not any one branch's.
    assert_row_at_line_refutes(MIR_DEADENTRY_PRE, is_bounds, 6, "deadentry_pre b[y]");
}

// ── THE PRICE, MEASURED ────────────────────────────────────────────────────
//
// Counting a parameter's ENTRY definition unconditionally costs these rows on
// programs that never panic. Each was `Proved` AND kernel-certified on the PRISTINE
// stage2 and while the liveness relaxation stood; the verdict on each row below is
// what the seam gives now, measured through `trust_vcgen::generate_vcs` +
// `Router::deterministic_in_process_ay` + `trust_certify::certify_vc`.
//
// TWO OF THEM ARE FALSE REFUTATIONS, not declines. That is the worst shape a
// precision loss can take and it is recorded here rather than softened: a correct
// program is reported as failing. It is still not a reason to keep an unsound fact —
// a false refutation is visible and wrong, a false proof is invisible and wrong.
//
// Every runtime-oracle ratio below is 0 panics: stock rustc, `-O -C
// debug-assertions=on`, `#[inline(never)]`, `black_box`, `catch_unwind`, with the
// reassigned parameter swept over `{0, 1, 3, 4, 1_000_000, usize::MAX}` — the entry
// values a caller could actually pass — crossed with the other inputs named.

/// `pub fn u_mod(mut k: usize, a: usize, arr: &[u8;4]) -> u8 { k = a % 4; arr[k] }`
/// Runtime oracle: 0/96 panicked (k x a in 0..16).
///
/// KEPT, as of 2026-11-07 — renamed from `..._loses_its_modulo_bound`, the move
/// `u_mask` made on 2026-09-13. `a % 4` is in `0..=3` and the array has 4 elements,
/// so proving this index is the CORRECT answer; the old `assert_undecided` pinned a
/// solver limitation. It was recorded as a DECLINE: ay found the refutation of
/// `k#s1_0 = Rem(a, 4) ∧ _5 = k#s1_0 ∧ _5 >= 4` and then rejected its own proof
/// (`unknown: (incomplete self-check-rejected) (1 conflicts)
/// [stop-item:unverified-trust-rule]`). Trust `0322559adc` ("Advance the public AY
/// IR CG Clean and MC development inputs", `first-party/ay` `40eb461a07` ->
/// `d9d1bbb64a`) moved ay past the commit that checks the remainder step, ay
/// `9695abae1` ("Check complete small remainder cases on the exact source"; see
/// `param_entry_gate.rs`, `param_modulo_bound_still_refutes`, for the sites and the
/// revert measurement), and the row is now `Proved` and kernel-certified. It is
/// proved from the def-site definition of `k`, not from a fact keyed on the bare
/// parameter, so the entry-def budget this section measures is not what changed.
#[test]
fn an_unconditionally_stored_parameter_keeps_its_modulo_bound() {
    let rows = rows_of(MIR_U_MOD, is_bounds);
    assert!(
        rows.iter().all(|(r, certified)| is_proved(r) && *certified),
        "u_mod: `a % 4` indexes a [u8;4] in range — this row must PROVE and \
         kernel-certify; got {rows:?}"
    );
    assert_all_proved_and_certified(MIR_U_MOD, "u_mod");
}

/// `pub fn u_mask(mut k: usize, a: usize, arr: &[u8;4]) -> u8 { k = a & 3; arr[k] }`
/// Runtime oracle: 0/96 panicked (k x a in 0..16).
///
/// KEPT, as of 2026-09-13 — and the rename is the point. `a & 3` is in `0..=3` and the
/// array has 4 elements, so this index is genuinely in range: proving it is the CORRECT
/// answer, and the old `assert_undecided` pinned a SOLVER LIMITATION rather than a
/// safety property. Main advanced `ay` by 43 commits (constant-index/bitmask reasoning)
/// and the limitation lifted. The modulo twin `u_mod` still declined then (recovered
/// 2026-11-07 by a different ay change), so the gain was specific rather than a blanket
/// strengthening. A test that pins an incapacity fails the
/// day the compiler improves; this one now asserts the fact instead.
///
/// ROOT-CAUSED 2026-09-19, after two rounds had recorded it only as "a red row
/// attributed to an ay incompleteness on bitmask bounds". It is one, and it is
/// SPECIFIC. `trust_vcgen` renders the masked definition as
/// `Eq(k#s0_0, BvToInt(BvAnd(IntToBv(a, 64), IntToBv(3, 64)), 64, false))`, and ay's
/// `TermStore::mk_bv2nat` rewrites that exact masked residue to `(mod a 4)` AT
/// INTERNING TIME — so the query reaches the executor with NO BITVECTOR IN IT and an
/// Int `mod`. `native_lane_logic` names the query `QF_UFBVLIA`, one of ay's
/// fail-closed combined logics, whose closed admission predicate listed
/// `has_int_div_mod` as unconditionally out of slice; the residue therefore forced
/// `LogicCategory::Other` and a fail-closed `unknown (incomplete)`. Admission was
/// NON-MONOTONE in the declared logic name: the same three assertions under
/// `QF_LIA` answered `unsat`.
///
/// Fixed in ay at `712f6b203` ("admission was non-monotone in the declared logic
/// name"), which fences `has_int_div_mod` only while a bitvector is actually live.
///
/// NOT A PRODUCT DEFECT AT THE COMPILER SURFACE — measured, not assumed. The
/// deployed stage1 compiler proves and kernel-certifies this program today:
/// `trustc --edition 2021 --crate-type lib -Ztrust-policy=certify` on
/// `pub fn u_mask(mut k: usize, a: usize, arr: &[u8; 4]) -> u8 { k = a & 3; arr[k] }`
/// reports "1 proved, 0 failed ... out of 1", "of which 1 kernel-certified". The
/// loss is confined to `Router::deterministic_in_process_ay`, the single-backend
/// seam router this test uses, which is strictly weaker than the compiler's
/// deployed set.
#[test]
fn an_unconditionally_stored_parameter_keeps_its_bitmask_bound() {
    let rows = rows_of(MIR_U_MASK, is_bounds);
    assert!(
        rows.iter().all(|(r, _)| is_proved(r)),
        "u_mask: `a & 3` indexes a [u8;4] in range — this row must PROVE; got {rows:?}"
    );
}

/// `pub fn u_div(mut k: usize, arr: &[u8;4]) -> u8 { k = 4 / 2; arr[k] }`
/// Runtime oracle: 0/6 panicked (k).
///
/// KEPT WHOLE as of 2026-09-19 — proof AND kernel certificate. It had been "kept as a
/// proof, lost as a certificate": the row proved, and the clean-kernel re-check no
/// longer certified it, which this test pinned as part of the measured price with a
/// note that recovering it was an improvement to promote rather than absorb.
///
/// PROMOTED, and the mechanism is specific. `k = 4 / 2` is a CLOSED CONSTANT
/// EXPRESSION, so `guards::extract_block_definitions_until_impl` now defines `k` to
/// the literal `2` the machine computes (the negation-lane spelling fix) instead of
/// rendering a division whose operands the certificate lane then has to re-derive.
/// The bound `k < 4` on a `[u8; 4]` follows from `k == 2` by evaluation, which is what
/// the kernel re-check can carry. The price note's other rows are untouched: a
/// reassignment with a VARIABLE in it (`k = a % 4`, `k = a & 3`) folds to nothing and
/// still pays.
#[test]
fn an_unconditionally_stored_parameter_keeps_its_division_proof_and_certificate() {
    let rows = rows_of(MIR_U_DIV, is_bounds);
    assert!(rows.iter().all(|(r, _)| is_proved(r)), "u_div must still prove; got {rows:?}");
    assert!(
        rows.iter().all(|(_, certified)| *certified),
        "u_div's kernel certificate came back with the closed-constant definition of \
         `k`; losing it again is a precision regression, not a neutral change. Got \
         {rows:?}"
    );
}

/// `pub fn u_clampcast(mut k: usize, a: i32, arr: &[u8;4]) -> u8 {
///      k = a.clamp(0, 3) as usize; arr[k] }`
/// Runtime oracle: 0/60 panicked (k x a in
/// {i32::MIN, -7, -1, 0, 1, 2, 3, 4, 100, i32::MAX}).
/// RECOVERED. This row was recorded as the budget's FALSE REFUTATION — `IndexOutOfBounds`
/// `Failed` on a counterexample naming the ENTRY `k` the body never reads. It is now
/// `Proved` and kernel-certified, because the fact reaches the row under a def-site
/// version instead of the two-valued bare `k`. `assert_false_refutation` exists to make
/// exactly this show up as a failure to promote, so it is promoted here rather than
/// absorbed. Its modulo and bitmask twins were recovered later
/// (`an_unconditionally_stored_parameter_keeps_its_modulo_bound`,
/// `an_unconditionally_stored_parameter_keeps_its_bitmask_bound`).
///
/// Since 2026-10-02 the literal `a.clamp(0, 3)` also mints its DECIDED `Ord::clamp: min >
/// max` row (KNOWN_HAZARDS "`certify` exits 0 on a literal `clamp`"); before, it minted
/// nothing. That row must PROVE; it is not kernel-certified because an `Assertion` row is
/// refused kernel authority by kind (`VcKind::kernel_authority_refusal`), exactly as the
/// guarded `clamp` row already was. Every other row keeps the proof AND the certificate.
#[test]
fn an_unconditionally_stored_parameter_falsely_refutes_its_cast_bound() {
    let mut saw_clamp_row = false;
    for (kind, verdict, certified) in verdicts(MIR_U_CLAMPCAST) {
        let decided_clamp = matches!(&kind,
            VcKind::Assertion { message } if message == "Ord::clamp: min > max");
        saw_clamp_row |= decided_clamp;
        assert!(is_proved(&verdict), "u_clampcast: {kind:?} got {verdict:?}");
        assert!(
            certified || decided_clamp,
            "u_clampcast: {kind:?} lost its certificate: {verdict:?}"
        );
    }
    assert!(saw_clamp_row, "u_clampcast: the literal clamp must mint its decided row");
}

/// `pub fn u_enumtag(mut k: usize, e: E, arr: &[u8;4]) -> u8 { k = e as usize; arr[k] }`
/// Runtime oracle: 0/12 panicked (k x e in {A, B}).
/// NOT LOST: still `Proved` and kernel-certified. The discriminant-variant range fact
/// is keyed on the tag temp, not on the reassigned parameter, so the count never
/// gated it.
#[test]
fn an_unconditionally_stored_parameter_keeps_its_enum_tag_bound() {
    assert_all_proved_and_certified(MIR_U_ENUMTAG, "u_enumtag");
}

/// `pub fn u_flat(mut i: usize, g: &[u8;6]) -> u8 { let mut s = 0u8;
///      for y in 0..2 { for x in 0..3 { i = y*3+x; s = s.wrapping_add(g[i]); } } s }`
/// Runtime oracle: 0/6 panicked (i).
/// RECOVERED 2026-09-29. This row was recorded as a FALSE REFUTATION on the
/// `IndexOutOfBounds` row: the loop payloads' yield facts `0 <= y < 2` and `0 <= x < 3`
/// reached only blocks that name `y` or `x`, not the block computing `y*3+x` through
/// its checked temps. They now also reach blocks naming a single-assignment local
/// computed from a payload (`iterator_yield::locals_derived_from`), so the row is
/// `Proved` and kernel-certified. Measured: without that change this row still
/// refutes. `assert_false_refutation` exists to make exactly this show up as a failure
/// to promote, so it is promoted here rather than absorbed.
#[test]
fn a_loop_body_stored_parameter_falsely_refutes_its_flattened_index_bound() {
    assert_all_proved_and_certified(MIR_U_FLAT, "u_flat");
}

/// The `[overflow:mul]` / `[overflow:add]` control for `u_flat`: the mul and add
/// results are BODY TEMPS, so their proofs must survive the PARAMETER budget
/// untouched — which they do; the parameter budget never reached them. (This row
/// said the loss above was confined to the index fact; since 2026-09-29 there is no
/// loss above.)
#[test]
fn flat_index_merge_keeps_the_mul_result_proof() {
    for (kind, verdict, certified) in verdicts(MIR_U_FLAT) {
        if is_bounds(&kind) || matches!(kind, VcKind::Unreachable) {
            continue;
        }
        assert!(
            is_proved(&verdict) && certified,
            "u_flat: {kind:?} is a body temp and must stay proved and certified; \
             got {verdict:?} certified={certified}"
        );
    }
}

/// `pub fn u_checkedsub(mut hi: usize, n: usize, arr: &[u8;4]) -> u8 {
///      if n <= 3 { hi = 3 - n; arr[hi] } else { 0 } }`
/// Runtime oracle: 0/48 panicked (hi x n in 0..8).
/// NOT LOST: both rows still `Proved`. PRISTINE stage2 kernel-certifies NEITHER (the
/// strict-certification boundary, unrelated to this lane), so this row asserts the
/// verdicts only.
#[test]
fn a_guarded_arm_stored_parameter_keeps_its_checked_sub_bound() {
    for (verdict, _) in rows_of(MIR_U_CHECKEDSUB, is_bounds) {
        assert!(is_proved(&verdict), "u_checkedsub: got {verdict:?}");
    }
}

// ── W5/W7: THE RESOLVER FAMILY, not the counters ───────────────────────────
//
// The seam swept def COUNTERS ("how many values can this local hold?"). RESOLVERS ask
// "what VALUE does this local hold?" and hand back a constant, a definition or a
// formula. They are the more dangerous half of the same class, for the reason
// `local_defs::body_unique_value_def`'s own doc gives: a resolver's answer is INLINED
// — into a place NAME, or into a SwitchInt edge fact — so version renaming has nothing
// left to rebind once the wrong value is in the formula. Both rows below were PROVED
// and KERNEL-CERTIFIED at PRISTINE 70a7534fd1 and with the counter seam applied.

/// `-Ztrust-dump=mir` capture, PRISTINE 70a7534fd1 stage2, of
///
/// ```ignore
/// pub fn p5(mut i: usize, c: bool) -> u8 {
///     let a = [9u8, 1, 9, 9];
///     let b = [7u8, 7, 7, 7];
///     if c { i = 1; }
///     if i > 3 { return 0; }
///     b[a[i] as usize]
/// }
/// ```
///
/// `index_local_const(func, i)` saw ONE whole-local `Assign` of the parameter `i` — the
/// constant `1` — and returned it, so `constant_array_index_segment` rendered the read
/// `a[i]` as the literal's element name `a[1;min=4]`, which the aggregate fact pins to
/// `1`. `b[1]` is in bounds, so the OUTER index proved. The `c == false` path reads
/// `a[0] == 9` and indexes `b[9]`.
const MIR_P5_CONST_INDEX: &str = r##"{"name":"p5","def_path":"p5::p5","span":{"file":"src/p5.rs","line_start":2,"col_start":0,"line_end":8,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":2,"ty":"Bool","name":"c"},{"index":3,"ty":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}},"name":"a"},{"index":4,"ty":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}},"name":"b"},{"index":5,"ty":"Bool","name":null},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":8,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":9,"ty":"Bool","name":null},{"index":10,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"StorageLive":3},{"Assign":{"place":{"local":3,"projections":[]},"rvalue":{"Aggregate":["Array",[{"Constant":{"Uint":[9,8]}},{"Constant":{"Uint":[1,8]}},{"Constant":{"Uint":[9,8]}},{"Constant":{"Uint":[9,8]}}]]},"span":{"file":"src/p5.rs","line_start":3,"col_start":12,"line_end":3,"col_end":32}}},{"StorageLive":4},{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"Aggregate":["Array",[{"Constant":{"Uint":[7,8]}},{"Constant":{"Uint":[7,8]}},{"Constant":{"Uint":[7,8]}},{"Constant":{"Uint":[7,8]}}]]},"span":{"file":"src/p5.rs","line_start":4,"col_start":12,"line_end":4,"col_end":32}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":2,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"src/p5.rs","line_start":5,"col_start":7,"line_end":5,"col_end":8}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":1,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[1,64]}}},"span":{"file":"src/p5.rs","line_start":5,"col_start":11,"line_end":5,"col_end":16}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[{"StorageLive":5},{"StorageLive":6},{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":[]}}},"span":{"file":"src/p5.rs","line_start":6,"col_start":7,"line_end":6,"col_end":8}}},{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Gt",{"Move":{"local":6,"projections":[]}},{"Constant":{"Uint":[3,64]}}]},"span":{"file":"src/p5.rs","line_start":6,"col_start":7,"line_end":6,"col_end":12}}}],"terminator":{"SwitchInt":{"discr":{"Move":{"local":5,"projections":[]}},"targets":[[0,4]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"src/p5.rs","line_start":6,"col_start":7,"line_end":6,"col_end":12}}}},{"id":3,"stmts":[{"StorageDead":6},{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"src/p5.rs","line_start":6,"col_start":22,"line_end":6,"col_end":23}}},{"StorageDead":5},{"StorageDead":4},{"StorageDead":3}],"terminator":{"Goto":7}},{"id":4,"stmts":[{"StorageDead":6},{"StorageDead":5},{"StorageLive":7},{"StorageLive":8},{"Assign":{"place":{"local":9,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":1,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"src/p5.rs","line_start":7,"col_start":6,"line_end":7,"col_end":10}}}],"terminator":{"Assert":{"cond":{"Move":{"local":9,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":5,"span":{"file":"src/p5.rs","line_start":7,"col_start":6,"line_end":7,"col_end":10},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"Use":{"Copy":{"local":3,"projections":[{"Index":1}]}}},"span":{"file":"src/p5.rs","line_start":7,"col_start":6,"line_end":7,"col_end":10}}},{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"Cast":[{"Move":{"local":8,"projections":[]}},{"Int":{"width":64,"signed":false}}]},"span":{"file":"src/p5.rs","line_start":7,"col_start":6,"line_end":7,"col_end":19}}},{"StorageDead":8},{"Assign":{"place":{"local":10,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":7,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"src/p5.rs","line_start":7,"col_start":4,"line_end":7,"col_end":20}}}],"terminator":{"Assert":{"cond":{"Move":{"local":10,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":6,"span":{"file":"src/p5.rs","line_start":7,"col_start":4,"line_end":7,"col_end":20},"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":[{"Index":7}]}}},"span":{"file":"src/p5.rs","line_start":7,"col_start":4,"line_end":7,"col_end":20}}},{"StorageDead":4},{"StorageDead":3},{"StorageDead":7}],"terminator":{"Goto":7}},{"id":7,"stmts":[],"terminator":"Return"}],"arg_count":2,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// `-Ztrust-dump=mir` capture, PRISTINE 70a7534fd1 stage2, of
///
/// ```ignore
/// pub fn p7(a: &[u8; 4], mut c: bool, i: usize, q: bool) -> u8 {
///     if q { c = i < 4; }
///     if c { a[i] } else { 0 }
/// }
/// ```
///
/// `latest_same_block_bool_definition`'s cross-block fallback resolves a bool
/// discriminant through its UNIQUE defining block when that block `Goto`s forward,
/// justified by "a local with a single static definition dominates all its uses (MIR
/// never reads an uninitialized local)". That argument is false of a PARAMETER, which
/// is initialized at ENTRY: with `q == false` the definition never runs. The resolved
/// comparison `i < 4` was conjoined onto the `c == true` edge as a dominating guard and
/// discharged the bounds obligation on `a[i]`.
const MIR_P7_CROSS_BLOCK_BOOL: &str = r##"{"name":"p7","def_path":"p7::p7","span":{"file":"src/p7.rs","line_start":2,"col_start":0,"line_end":7,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"a"},{"index":2,"ty":"Bool","name":"c"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":4,"ty":"Bool","name":"q"},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":4,"projections":[]}},"targets":[[0,2]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"src/p7.rs","line_start":3,"col_start":7,"line_end":3,"col_end":8}}}},{"id":1,"stmts":[{"Assign":{"place":{"local":2,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"src/p7.rs","line_start":4,"col_start":8,"line_end":4,"col_end":17}}}],"terminator":{"Goto":2}},{"id":2,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":2,"projections":[]}},"targets":[[0,5]],"otherwise":3,"exhaustive_enum_unreachable":false,"span":{"file":"src/p7.rs","line_start":6,"col_start":7,"line_end":6,"col_end":8}}}},{"id":3,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":3,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"src/p7.rs","line_start":6,"col_start":11,"line_end":6,"col_end":15}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":4,"span":{"file":"src/p7.rs","line_start":6,"col_start":11,"line_end":6,"col_end":15},"unwind":"Continue"}}},{"id":4,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":["Deref",{"Index":3}]}}},"span":{"file":"src/p7.rs","line_start":6,"col_start":11,"line_end":6,"col_end":15}}}],"terminator":{"Goto":6}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"src/p7.rs","line_start":6,"col_start":25,"line_end":6,"col_end":26}}}],"terminator":{"Goto":6}},{"id":6,"stmts":[],"terminator":"Return"}],"arg_count":4,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// One `(location, verdict, kernel-certified)` row per matching VC. `p5` carries THREE
/// `IndexOutOfBounds` rows across TWO spans and only one of them is the row under test,
/// so [`rows_of`]'s kind filter is not selective enough; `p7` (one row) goes through the
/// same helper so both witnesses are read the same way.
fn located_rows(mir: &str, want: fn(&VcKind) -> bool) -> Vec<(u32, u32, VerificationResult, bool)> {
    let func: VerifiableFunction =
        serde_json::from_str(mir).expect("the captured MIR fixture must deserialize");
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let vcs = trust_vcgen::generate_vcs(&func);
            let router = test_router::deterministic_test_router();
            router
                .verify_all(&vcs)
                .into_iter()
                .filter(|(vc, _)| want(&vc.kind))
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc.location.col_start, vc.location.col_end, r, certified)
                })
                .collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

/// The rows at exactly `[col_start, col_end)` — the one access under test.
fn rows_at(
    mir: &str,
    want: fn(&VcKind) -> bool,
    col_start: u32,
    col_end: u32,
) -> Vec<(VerificationResult, bool)> {
    let rows: Vec<_> = located_rows(mir, want)
        .into_iter()
        .filter(|(s, e, _, _)| *s == col_start && *e == col_end)
        .map(|(_, _, r, c)| (r, c))
        .collect();
    assert!(!rows.is_empty(), "the obligation this row is about must be generated at all");
    rows
}

/// The one obligation must be refuted, with a counterexample, and not certified.
fn assert_refutes_at(mir: &str, col_start: u32, col_end: u32, what: &str) {
    let rows = rows_at(mir, is_bounds, col_start, col_end);
    assert!(
        rows.iter().all(|(r, _)| !is_proved(r)),
        "{what}: the resolver row is PROVED again; got {rows:?}"
    );
    assert!(
        rows.iter()
            .any(|(r, _)| matches!(r, VerificationResult::Failed { counterexample: Some(_), .. })),
        "{what}: the resolver row must be REFUTED with a counterexample, not merely \
         undecided; got {rows:?}"
    );
    assert!(rows.iter().all(|(_, c)| !c), "{what}: a REFUTED row may not be certified");
}

/// W5. Runtime oracle (stock rustc, `-O -C debug-assertions=on`, `#[inline(never)]`,
/// `black_box`, `catch_unwind`): 3 of 20 panic over
/// `i in {0,1,2,3,4,5,7,64,1_000_000,usize::MAX} x c in {false,true}`; first
/// `i=0 c=false`, "index out of bounds: the len is 4 but the index is 9".
/// Killed by mutant W5-REVERT (dropping the `is_parameter` arm at the end of
/// `index_local_const`), under which `b[a[i] as usize]` returns to Proved+certified.
#[test]
fn param_reassigned_once_const_index_still_refutes() {
    // `b[a[i] as usize]` — the OUTER index, columns 4..20 of line 7.
    assert_refutes_at(MIR_P5_CONST_INDEX, 4, 20, "p5");
}

/// The `a[i]` control for W5: the INNER index at columns 6..10 is genuinely guarded by
/// `if i > 3 { return 0 }`, and its `Assert` row must stay Proved+certified — the fix
/// must not be paid for by losing the guarded read. (The same span also carries a
/// second, PRE-EXISTING false refutation at PRISTINE; this row asserts only that the
/// proved one survives.)
#[test]
fn const_index_fix_keeps_the_guarded_inner_read_proof() {
    let rows = rows_at(MIR_P5_CONST_INDEX, is_bounds, 6, 10);
    assert!(
        rows.iter().any(|(r, c)| is_proved(r) && *c),
        "p5: the guarded `a[i]` Assert row must stay Proved and certified; got {rows:?}"
    );
}

/// W7. Runtime oracle: 6 of 40 panic over
/// `i in {0,1,2,3,4,5,7,64,1_000_000,usize::MAX} x c in {false,true} x q in
/// {false,true}`; first `i=4 c=true q=false`, "index out of bounds: the len is 4 but
/// the index is 4". Killed by mutant W7-REVERT (dropping the `is_parameter` arm before
/// the cross-block fallback in `latest_same_block_bool_definition`), under which `a[i]`
/// returns to Proved+certified.
#[test]
fn param_bool_reassigned_once_cross_block_guard_still_refutes() {
    assert_refutes_at(MIR_P7_CROSS_BLOCK_BOOL, 11, 15, "p7");
}

// ── X1/X2: THE CHANNEL SET, not the parameter ──────────────────────────────
//
// The two rounds before this one read the class as "a PARAMETER's entry definition is
// invisible". That is ONE channel. The class is INCOMPLETE DEFINITION ENUMERATION: a
// local receives a value through several channels and each round's scan saw a different
// subset. Both rows below are `Call`-DESTINATION blindness, in a body with no reassigned
// parameter at all, and both were live kernel-certified false proofs with the previous
// round's fix applied.
//
// THE CHANNEL SET IS NOT CLOSED HERE. A THIRD channel — the MUTABLE ALIAS
// (`LocalWrite::Escape`) — is STILL a live kernel-certified false proof through
// `local_defs::body_unique_value_def`, and there is deliberately no row for it below:
// the witness refutes only under a change that turns correct `for`-loop programs into
// refutations, so it is parked rather than shipped. The defect, its witness, its
// runtime oracle and what a real fix needs are written at the point of the defect —
// `body_unique_value_def`'s `Escape` arm — and in the parked report
// `escape-residual.md`. Do not read the absence of an X3 row as the channel being
// closed.

/// X1 — THE SEAM ITSELF. `-Ztrust-dump=mir` capture, PRISTINE 70a7534fd1 stage2,
/// `--crate-type=lib -O`, of
///
/// ```ignore
/// #[inline(never)] pub fn pick(c: bool) -> usize { if c { 4 } else { 9 } }
/// #[inline(never)] pub fn pmod(s: bool, c: bool, n: usize, b: &[u8;4]) -> u8 {
///     let mut m = 4usize; if s { m = pick(c); } b[n % m]
/// }
/// ```
///
/// At `-O` rustc does NOT route the call through a temp: bb0 holds `m = const 4` and
/// bb1's `Call` destination IS `m`. `body_unique_value_def` scanned `Statement::Assign`
/// only, resolved `m` to `4`, and `build_modulo_bound_facts` emitted `n % m < 4` — false
/// on the `s = true, c = false` edge where `m` is `9`. The BOUNDS row was `Proved` and
/// kernel-certified at the base; only `[remzero]` failed.
///
/// Runtime oracle (stock rustc, `-O -C debug-assertions=on`, `#[inline(never)]`,
/// `black_box`, `catch_unwind`, panic hook silenced): 5 of 44 panic over
/// `n in {0,1,2,3,4,5,7,8,64,1_000_000,usize::MAX} x s in {false,true} x c in
/// {false,true}`; first `n=4 s=true c=false`, "index out of bounds: the len is 4 but the
/// index is 4".
const MIR_X1_CALL_DEST_MODULO: &str = r##"{"name":"pmod","def_path":"x1::pmod","span":{"file":"x1.rs","line_start":4,"col_start":0,"line_end":6,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":"Bool","name":"s"},{"index":2,"ty":"Bool","name":"c"},{"index":3,"ty":{"Int":{"width":64,"signed":false}},"name":"n"},{"index":4,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"b"},{"index":5,"ty":{"Int":{"width":64,"signed":false}},"name":"m"},{"index":6,"ty":{"Int":{"width":64,"signed":false}},"name":null},{"index":7,"ty":"Bool","name":null},{"index":8,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[4,64]}}},"span":{"file":"x1.rs","line_start":5,"col_start":16,"line_end":5,"col_end":22}}}],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":1,"projections":[]}},"targets":[[0,3]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"x1.rs","line_start":5,"col_start":27,"line_end":5,"col_end":28}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"x1::pick","args":[{"Move":{"local":2,"projections":[]}}],"dest":{"local":5,"projections":[]},"target":2,"span":{"file":"x1.rs","line_start":5,"col_start":35,"line_end":5,"col_end":42},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":2,"stmts":[],"terminator":{"Goto":3}},{"id":3,"stmts":[{"StorageLive":6},{"Assign":{"place":{"local":7,"projections":[]},"rvalue":{"BinaryOp":["Eq",{"Copy":{"local":5,"projections":[]}},{"Constant":{"Uint":[0,64]}}]},"span":{"file":"x1.rs","line_start":5,"col_start":48,"line_end":5,"col_end":53}}}],"terminator":{"Assert":{"cond":{"Move":{"local":7,"projections":[]}},"expected":false,"msg":"RemainderByZero","target":4,"span":{"file":"x1.rs","line_start":5,"col_start":48,"line_end":5,"col_end":53},"unwind":"Continue"}}},{"id":4,"stmts":[{"Assign":{"place":{"local":6,"projections":[]},"rvalue":{"BinaryOp":["Rem",{"Copy":{"local":3,"projections":[]}},{"Move":{"local":5,"projections":[]}}]},"span":{"file":"x1.rs","line_start":5,"col_start":48,"line_end":5,"col_end":53}}},{"Assign":{"place":{"local":8,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":6,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"x1.rs","line_start":5,"col_start":46,"line_end":5,"col_end":54}}}],"terminator":{"Assert":{"cond":{"Move":{"local":8,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":5,"span":{"file":"x1.rs","line_start":5,"col_start":46,"line_end":5,"col_end":54},"unwind":"Continue"}}},{"id":5,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":4,"projections":["Deref",{"Index":6}]}}},"span":{"file":"x1.rs","line_start":5,"col_start":46,"line_end":5,"col_end":54}}},{"StorageDead":6}],"terminator":"Return"}],"arg_count":4,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["n","Int"]},{"Int":0}]},{"Le":[{"Var":["n","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// X2 — THE SAME BLINDNESS THREE LINES BELOW THE PREVIOUS ROUND'S FIX.
/// `-Ztrust-dump=mir` capture, PRISTINE 70a7534fd1 stage2, `--crate-type=lib -O`, of
///
/// ```ignore
/// #[inline(never)] fn g(q: bool) -> bool { q }
/// #[inline(never)] pub fn p8(a: &[u8;4], i: usize, q: bool) -> u8 {
///     let c; if q { c = g(q); } else { c = i < 4; } if c { a[i] } else { 0 }
/// }
/// ```
///
/// `#[inline(never)]` on BOTH functions is load-bearing: without it `-O` inlines `g`
/// into a constant `Assign` and `c` has two `Assign`s, which the old scan already
/// refused; without `-O` the call routes through a temp and `c` again has two `Assign`s.
/// With both, `c` has ONE `Assign` (bb3) and ONE `Call` destination (bb1).
/// `guards::latest_same_block_bool_definition`'s cross-block fallback counted only
/// `Assign` blocks, called `c` uniquely defined, and INLINED `i < 4` as the SwitchInt
/// edge fact. `c` is not a parameter, so the previous round's `is_parameter` bail — added
/// three lines above this scan — could not fire.
///
/// Runtime oracle, same protocol: 6 of 20 panic over
/// `i in {0,1,2,3,4,5,7,64,1_000_000,usize::MAX} x q in {false,true}`; first
/// `i=4 q=true`.
const MIR_X2_CALL_DEST_BOOL: &str = r##"{"name":"p8","def_path":"x2b::p8","span":{"file":"x2b.rs","line_start":4,"col_start":0,"line_end":6,"col_end":1},"body":{"locals":[{"index":0,"ty":{"Int":{"width":8,"signed":false}},"name":null},{"index":1,"ty":{"Ref":{"mutable":false,"inner":{"Array":{"elem":{"Int":{"width":8,"signed":false}},"len":4}}}},"name":"a"},{"index":2,"ty":{"Int":{"width":64,"signed":false}},"name":"i"},{"index":3,"ty":"Bool","name":"q"},{"index":4,"ty":"Bool","name":"c"},{"index":5,"ty":"Bool","name":null}],"blocks":[{"id":0,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Copy":{"local":3,"projections":[]}},"targets":[[0,3]],"otherwise":1,"exhaustive_enum_unreachable":false,"span":{"file":"x2b.rs","line_start":5,"col_start":14,"line_end":5,"col_end":15}}}},{"id":1,"stmts":[],"terminator":{"Call":{"func":"x2b::g","args":[{"Constant":{"Bool":true}}],"dest":{"local":4,"projections":[]},"target":2,"span":{"file":"x2b.rs","line_start":5,"col_start":22,"line_end":5,"col_end":26},"atomic":null,"is_foreign":false,"is_unsafe_sig":false,"unwind":"Continue"}}},{"id":2,"stmts":[],"terminator":{"Goto":4}},{"id":3,"stmts":[{"Assign":{"place":{"local":4,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"x2b.rs","line_start":5,"col_start":37,"line_end":5,"col_end":46}}}],"terminator":{"Goto":4}},{"id":4,"stmts":[],"terminator":{"SwitchInt":{"discr":{"Move":{"local":4,"projections":[]}},"targets":[[0,7]],"otherwise":5,"exhaustive_enum_unreachable":false,"span":{"file":"x2b.rs","line_start":5,"col_start":53,"line_end":5,"col_end":54}}}},{"id":5,"stmts":[{"Assign":{"place":{"local":5,"projections":[]},"rvalue":{"BinaryOp":["Lt",{"Copy":{"local":2,"projections":[]}},{"Constant":{"Uint":[4,64]}}]},"span":{"file":"x2b.rs","line_start":5,"col_start":57,"line_end":5,"col_end":61}}}],"terminator":{"Assert":{"cond":{"Move":{"local":5,"projections":[]}},"expected":true,"msg":"BoundsCheck","target":6,"span":{"file":"x2b.rs","line_start":5,"col_start":57,"line_end":5,"col_end":61},"unwind":"Continue"}}},{"id":6,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Copy":{"local":1,"projections":["Deref",{"Index":2}]}}},"span":{"file":"x2b.rs","line_start":5,"col_start":57,"line_end":5,"col_end":61}}}],"terminator":{"Goto":8}},{"id":7,"stmts":[{"Assign":{"place":{"local":0,"projections":[]},"rvalue":{"Use":{"Constant":{"Uint":[0,8]}}},"span":{"file":"x2b.rs","line_start":5,"col_start":71,"line_end":5,"col_end":72}}}],"terminator":{"Goto":8}},{"id":8,"stmts":[],"terminator":"Return"}],"arg_count":3,"return_ty":{"Int":{"width":8,"signed":false}}},"contracts":[],"preconditions":[{"And":[{"Ge":[{"Var":["i","Int"]},{"Int":0}]},{"Le":[{"Var":["i","Int"]},{"Int":18446744073709551615}]}]}],"postconditions":[],"spec":{"requires":[],"ensures":[],"invariants":[]}}"##;

/// X1. Killed by mutant X1-REVERT (making `LocalWrite::WholeOpaque` non-ambiguous in
/// `local_defs::body_unique_value_def`), under which the bounds row returns to
/// `Proved` + kernel-certified.
#[test]
fn call_dest_reassigned_modulo_divisor_still_refutes() {
    assert_refutes(&MIR_X1_CALL_DEST_MODULO, is_bounds, "X1 pmod b[n % m]");
}

/// X2. Killed by mutant X2-REVERT (restoring the `Statement::Assign`-only `defines_here`
/// scan in `guards::latest_same_block_bool_definition` in place of
/// `local_defs::unique_defining_block`), under which `a[i]` returns to `Proved` +
/// kernel-certified.
#[test]
fn call_dest_defined_bool_cross_block_guard_still_refutes() {
    assert_refutes(&MIR_X2_CALL_DEST_BOOL, is_bounds, "X2 p8 a[i]");
}
