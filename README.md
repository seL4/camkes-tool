Visualisation of Componentised Operating Systems
================================================

This repository houses the work for the Taste of Research project. The aim is to visualise the components in a componentised system like CAmkES. This project will be done for CAmkES. Ideally the final result will be a GUI application, from which a "main".camkes file will be read. From here, the camkes-tool parser will generate an ASTObject (LiftedAST), and this application will allow you to visualise, modify and create CAmkES application with a mouse. Of course, the project will be done in steps - documented below.

![An ambitious final GUI App](http://bitbucket.keg.ertos.in.nicta.com.au/users/sthasarathan/repos/visualcomponents/browse/doc/images/Ambitious%20Overview.JPG)

To keep a picture in my mind of what this app could achieve. The app could display the components on the left, and allow the user to edit their C files on the right. This feels quite ambitious. However the main focus will be to visualise the components. 
Most likely however, this app will just have the visual graph part. The following will be a list of milestones I want to achieve. And I will indicate what I'm up to with (some arrow)

– – – – – – – 

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
...



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


– – – – – – – –


Milestone 2
-----------

The goal of milestone is to be able to move around the components and edit them. Then it should be possible to see the edits on the camkes files.
Milestone 1 only required a really basic graph drawing. Part of this milestone is to pretty it up to make it aesthestically pleasing.

### Things to do
1. 
