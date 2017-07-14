#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# Copyright 2017, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)

from PyQt5 import QtWidgets, QtGui, QtCore

class SaveOptionDialog(QtWidgets.QDialog):

    PNG = 0
    SVG = 1

    # --- PROPERTIES ---

    @property
    def picture_type(self):
        """
        :return: Integer of whether user choose PNG or SVG. Use class PNG and SVG #defines.
        """

        return self.format_combobox.currentIndex()

    @property
    def user_width(self):
        """
        PNG only
        :return: Integer of user's definied width. Default is 0
        """

        try:
            return int(self.width_lineedit.text())
        except:
            return 0

    @property
    def user_height(self):
        """
        PNG only
        :return: Integer of user's defined height. Default is 0
        """

        try:
            return int(self.height_lineedit.text())
        except:
            return 0

    @property
    def user_title(self):
        """
        SVG only
        :return: String of user's chosen title.
        """

        return self.title_lineedit.text()

    @property
    def user_description(self):
        """
        SVG only
        :return: String of user's chosen description
        """

        return self.descrip_textedit.toPlainText()

    # --- INITIALISATION ---

    def __init__(self, parent, proportional_rect=None):
        """
        Creates a Dialog box specifically for asking user whether they want a PNG or SVG file.
        If user wants SVG file - user has the option to give it a Title and Description for within the SVG file.
        If user wants PNG file - user has the option to give a width and height
        :param parent: Parent of this QDialog
        :param proportional_rect: The rectangle of the graph for which the image will be proportional to.
        :return:
        """

        super(SaveOptionDialog, self).__init__(parent)

        # ComboBox for choosing PNG or SVG
        self.format_combobox = QtWidgets.QComboBox(self)
        self.format_combobox.setInsertPolicy(QtWidgets.QComboBox.InsertAtBottom)
        self.format_combobox.addItem("Portable Network Graphics (*.png)")
        self.format_combobox.addItem("Scalable Vector Graphics (*.svg)")

        self.format_combobox.currentIndexChanged.connect(self.combox_changed)

        main_layout = QtWidgets.QVBoxLayout(self)
        main_layout.addWidget(self.format_combobox)

        # PNG Options

        self.png_options_widget = QtWidgets.QWidget(self)
        png_option_layout = QtWidgets.QVBoxLayout()

        # ^- Width

        width_label = QtWidgets.QLabel("Width: ")
        px_label = QtWidgets.QLabel("px")
        self.width_lineedit = self.__new_int_line_edits__("Width in pixels")
        self.width_lineedit.textEdited.connect(self.width_changed)
        width_label.setBuddy(self.width_lineedit)

        width_hlayout = QtWidgets.QHBoxLayout()
        width_hlayout.addWidget(width_label)
        width_hlayout.addWidget(self.width_lineedit)
        width_hlayout.addWidget(px_label)

        png_option_layout.addLayout(width_hlayout)

        # ^- Height

        height_label = QtWidgets.QLabel("Height: ")
        px_label2 = QtWidgets.QLabel("px")
        self.height_lineedit = self.__new_int_line_edits__("Height in pixels")
        self.height_lineedit.textEdited.connect(self.height_changed)
        height_label.setBuddy(self.height_lineedit)

        height_hlayout = QtWidgets.QHBoxLayout()
        height_hlayout.addWidget(height_label)
        height_hlayout.addWidget(self.height_lineedit)
        height_hlayout.addWidget(px_label2)

        png_option_layout.addLayout(height_hlayout)

        self.proportional_checkbox = QtWidgets.QCheckBox()
        self.proportional_checkbox.setText("Scale proportionally")
        self.proportional_checkbox.stateChanged.connect(self.proportional_state_change)

        png_option_layout.addWidget(self.proportional_checkbox)

        self.png_options_widget.setLayout(png_option_layout)
        main_layout.addWidget(self.png_options_widget)

        # SVG Options

        self.svg_option_widget = QtWidgets.QWidget(self)

        svg_option_layout = QtWidgets.QVBoxLayout()

        title_label = QtWidgets.QLabel("Title")
        self.title_lineedit = QtWidgets.QLineEdit()
        self.title_lineedit.setPlaceholderText("Type your title here")
        title_label.setBuddy(self.title_lineedit)

        svg_option_layout.addWidget(title_label)
        svg_option_layout.addWidget(self.title_lineedit)
        svg_option_layout.addSpacing(10)

        description_label = QtWidgets.QLabel("Description")
        self.descrip_textedit = QtWidgets.QTextEdit()
        self.descrip_textedit.setPlaceholderText("Type your description here")
        description_label.setBuddy(self.descrip_textedit)

        svg_option_layout.addWidget(description_label)
        svg_option_layout.addWidget(self.descrip_textedit)

        self.svg_option_widget.setLayout(svg_option_layout)

        main_layout.addWidget(self.svg_option_widget)

        self.svg_option_widget.setVisible(False)

        # Ok and Cancel buttons

        button_box = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.Ok | QtWidgets.QDialogButtonBox.Cancel)
        button_box.accepted.connect(self.accept)
        button_box.rejected.connect(self.reject)

        main_layout.addWidget(button_box)

        self.setLayout(main_layout)

        if proportional_rect:
            self.proportional_rect = proportional_rect

    # --- EVENTS ---

    def combox_changed(self, new_index):
        """
        Handles changes in the chosen format. Shows correct options for newly chosen format
        :param new_index: The new format chosen.
        """

        if new_index == self.PNG:
            self.svg_option_widget.setVisible(False)
            self.png_options_widget.setVisible(True)
        elif new_index == self.SVG:
            self.svg_option_widget.setVisible(True)
            self.png_options_widget.setVisible(False)

    def width_changed(self, text):
        """
        Handles changes to the width number given. If proportional is checked, height is also updated.
        :param text: new number in string format
        """

        if len(text) <= 0:
            return

        if self.proportional_checkbox.isChecked():
            assert isinstance(self.proportional_rect, QtCore.QRectF)
            width = int(text)
            height = self.proportional_rect.height() * width / self.proportional_rect.width()

            self.height_lineedit.setText(str(int(height)))

    def height_changed(self, text):
        """
        Handles changes to the height number given. If proportional is checked, width is also updated.
        :param text: new number in string format
        """

        if len(text) <= 0:
            return

        if self.proportional_checkbox.isChecked():
            assert isinstance(self.proportional_rect, QtCore.QRectF)
            height = int(text)
            width = self.proportional_rect.width() * height / self.proportional_rect.height()

            self.width_lineedit.setText(str(int(width)))

    def proportional_state_change(self, state):
        """
        If proportional is checked, height is updated based on width.
        :param state: New state of proportional button
        """

        if state == QtCore.Qt.Checked:
            width = self.user_width
            height = self.proportional_rect.height() * width / self.proportional_rect.width()
            self.width_lineedit.setText(str(int(width)))
            self.height_lineedit.setText(str(int(height)))

    def accept(self):
        """
        If Ok (or equivalent button) is pressed, all required fields are checked to see if valid inputs
        """

        # TODO: Highlight red the fields not complete

        if (self.width_lineedit.text() != "" and int(self.width_lineedit.text()) != 0 \
                and self.height_lineedit.text() != "" and int(self.height_lineedit.text()) != 0) \
                or self.format_combobox.currentIndex() == self.SVG:
            super(SaveOptionDialog, self).accept()

    # --- PRIVATE FUNCTIONS ---

    @staticmethod
    def __new_int_line_edits__(placeholder):
        """
        Helper Function for creating a QLineEdit object with placeholder and Integer Validation
        :param placeholder: Placeholder text to be shown in the textbox
        :return: QLineEdit object
        """
        line_edit = QtWidgets.QLineEdit()
        line_edit.setPlaceholderText(placeholder)
        line_edit.setValidator(QtGui.QIntValidator())

        return line_edit
