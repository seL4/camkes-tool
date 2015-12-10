Visualisation of Componentised Operating Systems
================================================

This repository houses the work for the Taste of Research project. The aim is to visualise the components in a componentised system like CAmkES. This project will be done for CAmkES. Ideally the final result will be a GUI application, from which a "main".camkes file will be read. From here, the camkes-tool parser will generate an ASTObject (LiftedAST), and this application will allow you to visualise, modify and create CAmkES application with a mouse. Of course, the project will be done in steps - documented below.

![An ambitious final GUI App](http://bitbucket.keg.ertos.in.nicta.com.au/users/sthasarathan/repos/visualcomponents/browse/doc/images/Ambitious%20Overview.JPG?raw)

To keep a picture in my mind of what this app could achieve. The app could display the components on the left, and allow the user to edit their C files on the right. This feels quite ambitious. However the main focus will be to visualise the components. 
Most likely however, this app will just have the visual graph part. The following will be a list of milestones I want to achieve. And I will indicate what I'm up to with (some arrow)

* * *

Milestone 1
-----------

The first milestone will be to read in a .camkes file, use the camkes-tool to parser and give an LiftedAST object, and display a static image of this to the screen. The app will be using objected-oriented design, to ensure it is easy to extend from milestone to milestone.
The obvious design principle to follow is Model-View-Controller. The repo will be divided into models in one folder, controllers in another folder and views in yet another folder.
First, for both the controller and the view, there needs to be a base class. 

### Controller
Controllers when instanciated, will load its models and views - and create a main view (widget is the terminolgy for GTK+ ). It should have a link to its parent controller (None if it doesn't have a parent), as well as a link to its root view. 
- __init__()
- parentController
- rootWidget

Views will be subclasses of DrawingArea (which is a subclass of widget). Subclasses will be formed for each ASTObject instances.

From here, the goal is to display the LiftedAST into a graph.

### Graph Drawing Theories
Using graphviz to do the heavy lifting.

### Things to do
1. Initialise the files with model, view, controller folders and associated files.
2. Set up PyCharm
3. Start creating the controller superclass
4. Create the graph controller subclass from the above. Also create a main function, so that it is possible to start the code from the file.
5. Attempt to make the controller give a simple window with a box say.
6. Read up on graph drawing theories.
7. Create a model to parse and interface witht the camkes-tools parser.
8. Create widget subclasses for each ASTObject type.
9. Create widget instances for each ASTObject, and dump them on the screen.
10. Use the graph drawing theory to place them in good locations. Draw connections and attempt to label them.


* * *

Milestone 2
-----------

The goal of milestone 2 is to display the components (instances) in a nice way, with all the info about the widgets. Widget should then be able to move around (as well as ability to pin them). 
Part of this milestone is to pretty it up to make it aesthestically pleasing. In the previous milestone, I found it unusually difficult to draw a line between two widgets. 
In the risk of wasting a lot of time (already wasted a day on it), I shall push connectors to milestone 3. Milestone 2 will focus on the instances themselves. 
A side task is to also put the root_widget into a scrolling window.

### Things to do
1. Create examples of camkes apps, which has made different component types.
1. Add extra arguments to graphviz, to make the graph more spread out (to give connectors extra space), having hardware graphs lower on the screen.
1. Currently the graph is draw inverted. This is because the co-ordinates of graphviz is true maths co-ords and not GUI co-ords. Need to translate between them.
1. Draw out components with all info. Chance to make it final and aesthically pleasing

### Notes: 
#### Info that a instance needs to display to the user
...

* * *

Features & Ideas
----------------

In the risk of losing the ideas suggested:
* List of all connectors and components on the sides. Then ability to draw from the list to create a new component or connector
* Using graphviz, and DOT graphing
* Ability to scroll and zoom the window
* Terminal (vim/nano) on one side for easy code editing
* Ability to save and reload graphs. Need to save positions of nodes.
