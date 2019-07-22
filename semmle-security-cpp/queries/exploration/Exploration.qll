private import cpp

/**
 * To get our bearings, we'll begin by pinning down some important types
 * in the GhostScript interpreter.
 */
module ImportantTypes {
  /*
   * A quick inspection of the code reveals that PostScript values are
   * represented by a type called `ref`. Let's find out what that is.
   */

  private query predicate isRawRefType(Type t) { t.hasName("ref") }

  /*
   * OK, so `ref` is a typedef to `ref_s`. Let's inspect that type as well,
   * and model some useful properties.
   */

  /**
   * The GhostScript `ref_s` type, holding a typed reference to a PostScript
   * object.
   */
  class GsRefType extends Class {
    GsRefType() { this.hasName("ref_s") }

    /*
     * The `ref_s` type has two members. The first is a `tas_s` -- a struct
     * which has a `type_attrs` field that indicates the type of the ref.
     * The second is a union across the possible values stored in this ref.
     * Reading from an unexpected branch of that union leads to type confusion.
     */

    /**
     * Gets the `tas` field, which holds, in its `type_attrs` field, the type tag.
     */
    Field getTasField() { result = this.getAField() and result.hasName("tas") }
    
    /**
     * Get a `type_attrs` access for  `qualifier`.
     */
    FieldAccess getATypeAttrsAccess(Expr qualifier) {
      exists(FieldAccess valueAccess |
        qualifier = valueAccess.getQualifier() and
        valueAccess = getTasField().getAnAccess() and
        result.getQualifier() = valueAccess and
        result.getTarget().hasName("type_attrs")
      )
    }

    /**
     * Gets the `value` field, which holds a union over the possible values.
     */
    Field getValueField() { result = this.getAField() and result.hasName("value") }

    /**
     * Get a typed access to the stored value on `qualifier`.
     */
    FieldAccess getATypedAccess(Expr qualifier) {
      exists(FieldAccess valueAccess |
        qualifier = valueAccess.getQualifier() and
        valueAccess = getValueField().getAnAccess() and
        result.getQualifier() = valueAccess
      )
    }
  }

  /*
   * How does user input get into the interpreter? Mainly by being put on the stack,
   * after which a built-in functino is invoked. Such builtin functions (called
   * "operators" in PostScript parlance) are registered with the interpreter, through
   * an `op_def` object:
   */

  private query predicate isOpRegistration(
    Class c, ClassAggregateLiteral l, Expr oname, FunctionAccess proc, Function func
  ) {
    c = l.getUnspecifiedType() and
    oname = l.getFieldExpr(any(Field f | f.hasName("oname"))) and
    proc = l.getFieldExpr(any(Field f | f.hasName("proc"))) and
    func = proc.getTarget()
  }

  /*
   * We can see that builtin operators are passed an `i_ctx_t` parameter. Let's
   * investigate what that contains.
   */

  private query predicate iCtxType(Type t) { t.hasName("i_ctx_t") }

  /*
   * It's a typedef to `gs_context_state_s`, which holds the global interpreter state.
   * Let's examine its members.
   */

  private query predicate iCtxMembers(Class c, Field f, Type ft) {
    c.hasName("gs_context_state_s") and f = c.getAField() and ft = f.getType()
  }

  /*
   * The most directly interesting fields are the three stacks: The dictionary stack
   * `dict_stack`, the execution stack `exec_stack` and the operand stack `op_stack`.
   * Each of those can be directly set up by malicious code, and data coming from
   * them should be considered untrusted.
   */

  /**
   * The type representing the global interpreter state.
   */
  class GsGlobalContext extends Class {
    GsGlobalContext() { this.hasName("gs_context_state_s") }

    /**
     * Get the `name` stack field (where `name` is one of `op`, `dict` or `exec`).
     */
    Field getStack(string name) { result = this.getAField() and result.hasName(name + "_stack") }

    /*
     * Each stack field contains a `stack` pointer to a `ref_stack_s`, within which
     * `p` is the current top of the stack.
     */

    /**
     * Gets an access to the named stack's top element (where `name` is one of `op`,
     * `dict` or `exec`). The access may be a read or write.
     */
    FieldAccess getAStackAccess(string name) {
      exists(FieldAccess stack |
        stack.getQualifier() = getStack(name).getAnAccess() and
        stack.getTarget().hasName("stack") and
        result.getQualifier() = stack and
        result.getTarget().hasName("p")
      )
    }
  }

  /*
   * Finally, we can model builtin operators, as they are easy entrypoints from
   * PostScript code.
   */

  /**
   * A function which implements a PostScript operator.
   */
  class GsOperator extends Function {
    StringLiteral descriptor;

    GsOperator() { isOpRegistration(_, _, descriptor, _, this) }

    StringLiteral getDescriptor() { result = descriptor }

    /**
     * Get a function called from this operator while passing through the global
     * context (which has index `ctxArg` as a parameter of the result).
     */
    Function getACalledFunction(int ctxArg) {
      result = this and ctxArg = 0
      or
      exists(Call call, Function prev, int prevIdx |
        call.getEnclosingFunction() = prev and
        prev = getACalledFunction(prevIdx) and
        call.getArgument(ctxArg) = prev.getParameter(prevIdx).getAnAccess() and
        result = call.getTarget()
      )
    }

    /**
     * Get the declared number of operands for this operator.
     */
    int getNumOperands() { result = descriptor.getValue().charAt(0).toInt() }

    /**
     * Get the PostScript-visible name of this operator.
     */
    string getPostScriptName() { result = descriptor.getValue().suffix(1) }

    /**
     * Holds if this operator isn't undefined at the end of `gs_init.ps`.
     */
    predicate isVisible() { not isUndefined() }

    /**
     * Holds if this operator is undefined from the global namespace in `gs_init.ps`.
     *
     * Such operators cannot be easily called from malicious PostScript code.
     */
    predicate isUndefined() { getPostScriptName() = External::getAnUndefinedOperator() }
  }
}

module Taint {
  import ImportantTypes
  private import semmle.code.cpp.dataflow.TaintTracking

  /*
   * At its simplest, a type confusion occurs when a `ref` value from one of the
   * global context stacks is read without a preceding type check. We can easily
   * phrase this as a local taint problem, in order to get a feeling for what
   * type checks we need to support:
   */

  private query predicate localOpRead(
    string stack, DataFlow::Node stackRead, DataFlow::Node typedRead
  ) {
    stackRead.asExpr() = any(GsGlobalContext c).getAStackAccess(stack) and
    typedRead.asExpr() = any(GsRefType t).getATypedAccess(_) and
    TaintTracking::localTaint(stackRead, typedRead) and
    not typedRead.asExpr() = any(Assignment a).getLValue()
  }

  /*
   * In order to model type checks, we'll have to define a global dataflow configuration.
   */

  class GsTypeConfusion extends TaintTracking::Configuration {
    string stack;

    GsTypeConfusion() {
      this = "GsTypeConfusion[" + stack + "]" and
      exists(any(GsGlobalContext c).getAStackAccess(stack))
    }

    override predicate isSource(DataFlow::Node source) {
      source.asExpr() = any(GsGlobalContext c).getAStackAccess(stack)
    }

    override predicate isSink(DataFlow::Node sink) {
      sink.asExpr() = any(GsRefType t).getATypedAccess(_) and
      not sink.asExpr() = any(Assignment a).getLValue()
    }
  }

  
  
  private query predicate typeConfusion(
    DataFlow::PathNode loc, DataFlow::PathNode source, DataFlow::PathNode sink, string msg,
    DataFlow::PathNode link, string linkText
  ) {
    any(GsTypeConfusion c).hasFlowPath(source, sink) and
    loc = sink and
    link = source and
    msg = "Typed use of stack data from $@." and
    linkText = link.toString()
  }
}

/**
 * External (that is, non-C) data.
 */
private module External {
  /**
   * List of operators that are explicitly undefined in `gs_init.ps`, and are therefore
   * not callable by user code.
   */
  string getAnUndefinedOperator() {
    result = ".callinstall" or
    result = ".callbeginpage" or
    result = ".callendpage" or
    result = ".currentstackprotect" or
    result = ".setstackprotect" or
    result = ".errorexec" or
    result = ".finderrorobject" or
    result = ".installsystemnames" or
    result = ".bosobject" or
    result = ".fontbbox" or
    result = ".type1execchar" or
    result = ".type2execchar" or
    result = ".type42execchar" or
    result = ".setweightvector" or
    result = ".getuseciecolor" or
    result = "processcolors" or
    result = ".includecolorspace" or
    result = ".execn" or
    result = ".instopped" or
    result = ".stop" or
    result = ".stopped" or
    result = ".setcolorrendering" or
    result = ".setdevicecolorrendering" or
    result = ".buildcolorrendering1" or
    result = ".builddevicecolorrendering1" or
    result = ".TransformPQR_scale_WB0" or
    result = ".TransformPQR_scale_WB1" or
    result = ".TransformPQR_scale_WB2" or
    result = ".currentoverprintmode" or
    result = ".copydevice2" or
    result = ".devicename" or
    result = ".doneshowpage" or
    result = ".getbitsrect" or
    result = ".getdevice" or
    result = ".getdefaultdevice" or
    result = ".getdeviceparams" or
    result = ".gethardwareparams" or
    result = "makewordimagedevice" or
    result = ".outputpage" or
    result = ".putdeviceparams" or
    result = ".setdevice" or
    result = ".currentshowpagecount" or
    result = ".setpagedevice" or
    result = ".currentpagedevice" or
    result = ".knownundef" or
    result = ".setmaxlength" or
    result = ".rectappend" or
    result = ".initialize_dsc_parser" or
    result = ".parse_dsc_comments" or
    result = ".fillCIDMap" or
    result = ".fillIdentityCIDMap" or
    result = ".buildcmap" or
    result = ".filenamelistseparator" or
    result = ".libfile" or
    result = ".getfilename" or
    result = ".file_name_combine" or
    result = ".file_name_is_absolute" or
    result = ".file_name_separator" or
    result = ".file_name_directory_separator" or
    result = ".file_name_current" or
    result = ".filename" or
    result = ".peekstring" or
    result = ".writecvp" or
    result = ".subfiledecode" or
    result = ".setupUnicodeDecoder" or
    result = ".jbig2makeglobalctx" or
    result = ".registerfont" or
    result = ".parsecff" or
    result = ".getshowoperator" or
    result = ".getnativefonts" or
    result = ".beginform" or
    result = ".endform" or
    result = ".get_form_id" or
    result = ".repeatform" or
    result = ".reusablestream" or
    result = ".rsdparams" or
    result = ".buildfunction" or
    result = ".sethpglpathmode" or
    result = ".currenthpglpathmode" or
    result = ".currenthalftone" or
    result = ".sethalftone5" or
    result = ".image1" or
    result = ".imagemask1" or
    result = ".image3" or
    result = ".image4" or
    result = ".getiodevice" or
    result = ".getdevparms" or
    result = ".putdevparams" or
    result = ".bbox_transform" or
    result = ".matchmedia" or
    result = ".matchpagesize" or
    result = ".defaultpapersize" or
    result = ".oserrno" or
    result = ".setoserrno" or
    result = ".oserrorstring" or
    result = ".getCPSImode" or
    result = ".getscanconverter" or
    result = ".setscanconverter" or
    result = ".type1encrypt" or
    result = ".type1decrypt.languagelevel" or
    result = ".setlanguagelevel" or
    result = ".eqproc" or
    result = ".fillpage" or
    result = ".saslprep" or
    result = ".shfill" or
    result = ".argindex" or
    result = ".bytestring" or
    result = ".namestring" or
    result = ".stringbreak" or
    result = ".stringmatch" or
    result = ".globalvmarray" or
    result = ".globalvmdict" or
    result = ".globalvmpackedarray" or
    result = ".globalvmstring" or
    result = ".localvmarray" or
    result = ".localvmdict" or
    result = ".localvmpackedarray" or
    result = ".localvmstring" or
    result = ".systemvmarray" or
    result = ".systemvmdict" or
    result = ".systemvmpackedarray" or
    result = ".systemvmstring" or
    result = ".systemvmfile" or
    result = ".systemvmlibfile" or
    result = ".systemvmSFD" or
    result = ".settrapparams" or
    result = ".currentsystemparams" or
    result = ".currentuserparams" or
    result = ".getsystemparam" or
    result = ".getuserparam" or
    result = ".setsystemparams" or
    result = ".setuserparams" or
    result = ".checkpassword" or
    result = ".locale_to_utf8" or
    result = ".currentglobal" or
    result = ".gcheck" or
    result = ".imagepath" or
    result = ".currentoutputdevice" or
    result = ".type" or
    result = ".writecvs" or
    result = ".setSMask" or
    result = ".currentSMask" or
    result = ".needinput" or
    result = ".countexecstack" or
    result = ".execstack" or
    result = "filterdict" or
    result = ".cidfonttypes" or
    result = ".colorrenderingtypes" or
    result = ".formtypes" or
    result = ".halftonetypes" or
    result = ".imagetypes" or
    result = ".imagemasktypes" or
    result = ".patterntypes" or
    result = ".shadingtypes" or
    result = ".wheredict" or
    result = ".renderingintentdict" or
    result = ".currentmatrix" or
    result = ".setmatrix" or
    result = ".setlinecap" or
    result = ".setlinejoin" or
    result = ".sizeimagebox" or
    result = ".systemvmcheck" or
    result = ".forceinterp_exit" or
    result = ".actonuel" or
    result = ".init_otto_font_file" or
    result = ".composefontdict" or
    result = ".type1build" or
    result = ".origdefinefont" or
    result = ".origundefinefont" or
    result = ".origfindfont" or
    result = ".buildnativefontmap" or
    result = ".completefont" or
    result = ".definefakefonts" or
    result = ".fontnameproperties" or
    result = ".growfontdict" or
    result = ".substitutefont" or
    result = ".substitutefontname" or
    result = ".FontDirectory" or
    result = ".charkeys" or
    result = ".makesfnts" or
    result = ".pickcmap" or
    result = ".loadttcidfont" or
    result = ".loadpdfttfont" or
    result = "obind" or
    result = "odef" or
    result = ".packtomark" or
    result = ".putdeviceprops" or
    result = ".growdict" or
    result = ".growdictlength" or
    result = ".userdict" or
    result = ".uservar" or
    result = ".getdefaulthalftone" or
    result = ".registererror" or
    result = ".PurgeDict" or
    result = ".runresource" or
    result = ".numicc_components" or
    result = ".set_outputintent" or
    result = ".internalstopped" or
    result = ".generate_dir_list_templates" or
    result = ".generate_dir_list_templates_with_length" or
    result = ".type11mapcid" or
    result = ".type9mapcid" or
    result = ".clearerror" or
    result = ".beginpage" or
    result = ".endpage" or
    result = ".getpath" or
    result = ".confirm" or
    result = ".confirmread"
  }
}
