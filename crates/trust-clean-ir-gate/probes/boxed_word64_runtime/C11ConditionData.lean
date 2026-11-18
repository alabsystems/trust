import Init
namespace C11ConditionData
def branch_0 : String := "#if defined(__STDC_VERSION__) && __STDC_VERSION__ > 201710L\nnewer\n#elif !defined(__cplusplus)\nselected\n#else\nother\n#endif\n"
end C11ConditionData
