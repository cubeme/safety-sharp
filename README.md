Welcome to the S# Modeling Framework
============

S# (pronounced "safety sharp") is a formal modeling and analysis framework for safety-critical systems.
It brings forward
well-established software engineering principles and best
practices to the modeling and analysis of safety-critical
systems during all phases of development. S# is an integrated approach that fosters the systematic development
of high-quality, comprehensible, adequate, and modular
models of such systems, while also allowing the use of
formal safety analysis techniques for rigorous safety assessment. In doing so, S # tackles many of the challenges
faced by safety engineers.

####Safety-Critical Systems
Safety-critical systems are expected to operate safely under regular circumstances as well as in many degraded situations. In the
latter case, these systems have to cope with one or more components that are not working as specified, while at the same time they
have to avoid (serious) economical or environmental damage, injuries, or even loss of lives. Fault Tree Analysis (FTA),
and Failure Modes and Effects Analysis (FMEA) are commonly used traditional
safety analysis techniques that help safety engineers in systematically analyzing the safety of a system: They dissect the
system to determine component faults that might result in a _hazard_; a potentially dangerous
situation that violates the intended behavior of the system.

The functionality provided by safety-critical systems is becoming increasingly complex, therefore requiring the
development of more sophisticated safety analysis techniques to analyze the system behavior in both regular and degraded
situations. Additionally, software is becoming a more important factor for the innovation of safety-critical systems; whether it
is the automotive sector, avionics, or the railway industry, more and more safety-critical hardware is replaced by or augmented
with software.
Among the typical reasons for this change in system design is the increased flexibility offered by implementing certain functionality in
software, resulting in a larger amount of features supported by the system as well as more full-fledged implementations of the
individual features. On the other hand, software development is complex and error-prone and is thus likely to introduce systematic
errors that have the potential of violating safety requirements.

####Why S#?
The S# modeling framework provides safety engineers with a modeling language specifically
designed to express important safety-related concepts such as _component faults_ and the _physical environment_ of a
safety-critical system.
For safety assessments, _model simulations_ as well as _formal safety analyses_ are supported. To assist safety
engineers in developing the models and using the analysis techniques, S# provides systematic modeling and analysis guidelines and offers a
sophisticated tool integration.

The S# modeling language and tool chain enables the models of safety-critical systems to become _executable
specifications_, allowing  iterative and incremental model development, simulation, testing, and
debugging.  
Additionally, S# models can be used to test-drive actual safety-critical software components of the system
under development by integrating these components into a S# simulation.

A prerequisite for the use of S#'s safety analysis capabilities are adequate models of the system to be analyzed.
Experience shows that adequacy is greatly influenced by the comprehensibility of the model, which in turn depends on the expressibility of the modeling language
as well as the level of abstraction used during modeling. Consequently, S# provides modeling language concepts, modeling
guidelines, and sophisticated tooling that help to improve the adequacy of models of 
safety-critical systems. It hides the details of the underlying formal analysis techniques, allowing the safety engineer
to concentrate on the creation of the models.
Additionally, recent developments like safety-critical product lines require more flexible modeling techniques to
conveniently express and configure different product configurations for formal safety analyses. This flexibility also helps with
exploring the design space of a safety-critical system early in its development and is fully supported by S#'s
modeling language, its analysis techniques, and its tooling.

Formal methods are S#'s foundation: Formal analysis techniques allow for sound reasoning about safety-critical aspects
of system designs with mathematical rigor. Our Deductive Cause Consequence Analysis (DCCA), for instance, is a fully automated formal analysis
technique based on model checking that computes the _minimal critical sets_ of component faults; that is, sets of
faults with the potential of causing a system hazard. DCCA
guarantees that all minimal critical sets are found and that they contain no "unnecessary" faults, i.e., faults that are
actually not required for the occurrence of the hazard.
Simply put, the use of formal methods ensures the adequacy of the results of safety analyses performed by S#.

####Modeling Language and Tool Support
Instead of inventing a completely new modeling language and corresponding tools, S# models are written in a domain
specific language (DSL) that is embedded into the C# programming language with full access to
all .NET libraries and tools. S#'s own analysis tools are integrated into Visual
Studi with
state-of-the-art code editing and debugging features.
Even though S# models are _represented_ as code, they are still models, albeit executable ones; conceptually, they are at a
higher level of abstraction than actual code.
The implementation of a safety-critical system's software is typically done in the C or C++ programming languages and compiled for
specific embedded microcontrollers -- S# does not try to change that.

The S# modeling language inherits all of C#'s language features and expressiveness.
Only the parts of a S# model that are intended to be used with a model checking based analysis technique are restricted
to a subset of C#.
For these parts, arbitrary object construction, certain built-in data types, loops, recursion as well as other more sophisticated
features such as LINQ or the ``await`` operator are not supported. 
For simulation-only models as well as for supporting
infrastructure code that sets up test cases or composes system design variants, however, none of these restrictions
apply. 
The expressiveness of the S# modeling language is therefore even greater for simulation-only models that are not
analyzed by model checking because of their size or due to a deliberate decision. Infrastructure code is not restricted in any
case.

It is
  up to the safety engineer to decide which features of S#'s modeling language and formal analyses are used for
 the development of a safety-critical
system. In fact, that decision can even vary based on the level of abstraction of a model: For instance, during the design
exploration phase, a safety engineer might first create a highly abstract model of the desired system behavior without component
faults, using model checking to analyze the functional correctness of the system. In a second step, component
faults could be added, now using model checking to analyze the safety of the system. Subsequently, the model could be gradually
refined to a less abstract, simulation-only one that takes advantage of all of S#'s expressiveness, even including the
actual system software or hardware during later stages of the implementation phase.
 Using software engineering best practices, test cases for the abstract model could be reused
during later stages of the development.

##Get Started
For the time being, S# is under heavy development. Usage and installation instructions will be available once some technical details are sorted out and stabilized, which should be around April/May 2015. We plan on publishing a NuGet package and a Visual Studio extension, making it easy to install, update, and use S#. More examples and case studies will be added in the coming weeks.

##Example
The following small sample shows the model of a pressure sensor using the S# modeling language. The sensor can be used to check whether a certain pressure level has been reached. The sample shows how safety-critical _components_ and their _required_ and _provided ports_ are declared using the C#-based DSL provided by S#. The model also includes a _component fault_ that prevents the sensor from reporting that the pressure level has been reached, possibly resulting in a hazard at the system level.
```C#
/// Represents a model of a pressure sensor.
class PressureSensor : Component 
{
  /// The pressure level that the sensor reports.
  private readonly int _pressure;
  
  /// Instantiates an instance of a pressure sensor. The maximum allowed pressure is 
  /// passed in as a constructor argument, allowing for easy configuration and 
  /// re-use of component models.
  public PressureSensor(int pressure)
  {
      this._pressure = pressure;
  }
  
  /// Required port. This is the port that the sensor uses to sense the actual 
  /// pressure level in some environment 
  public extern int CheckPhysicalPressure();
  
  /// Provided port. Indicates whether the pressure level that the sensor is 
  /// configured to report has been reached.
  public bool HasPressureLevelBeenReached() 
  {
      return CheckPhysicalPressure() >= _pressure;
  }
  
  /// Represents a transient fault (i.e., a fault that can come and go at any time) 
  /// that prevents the sensor from reporting the pressure correclty.
  [Transient] 
  class SenseNoPressure : Fault
  { 
      /// Overwrites the behavior of the sensor's provided port, always returning the 
      /// constant 'false' for as long as the fault is active/occurring.
      public bool HasPressureLevelBeenReached() 
      {
          return false; 
      }
  }
}
```
