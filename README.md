Visualisation of Componentised Operating Systems
================================================

This repository houses the work for the Taste of Research project. The aim is to visualise the components in a componentised system like CAmkES. This project will be done for CAmkES. Ideally the final result will be a GUI application, from which a "main".camkes file will be read. From here, the camkes-tool parser will generate an ASTObject (LiftedAST), and this application will allow you to visualise, modify and create CAmkES application with a mouse. Of course, the project will be done in steps - documented below.

![An ambitious final GUI App](./doc/images/Ambitious\ Overview.JPG)
To keep a picture in my mind of what this app could achieve. The app could display the components on the left, and allow the user to edit their C files on the right. This feels quite ambitious. However the main focus will be to visualise the components. 
Most likely however, this app will just have the visual graph part. The following will be a list of milestones I want to achieve. And I will indicate what I'm up to with (some arrow)


Milestone 1
-----------

The first milestone will be to read in a .camkes file, use the camkes-tool to parser and give an LiftedAST object, and display a static image of this to the screen. The app will be using objected-oriented design, to ensure it is easy to extend from milestone to milestone.
The obvious design principle to follow is Model-View-Controller. The repo will be divided into models in one folder, controllers in another folder and views in yet another folder.
First, for both the controller and the view, there needs to be a base class. 

## Controller
Controllers when instanciated, will load its models and views - and create a main view (widget is the terminolgy for GTK+ ). It should have a link to its parent controller (None if it doesn't have a parent), as well as a link to its root view. 
- __init__()
- parentController
- rootWidget

Views will be subclasses of DrawingArea (which is a subclass of widget). Subclasses will be formed for each ASTObject.

From here, the goal is to display the LiftedAST into a graph.

## Graph Drawing Theories
...
