<?xml version="1.0" encoding="UTF-8"?>
<!-- Generated with glade 3.18.3 -->
<interface>
  <requires lib="gtk+" version="3.12"/>
  <object class="GtkFrame" id="Instance_frame">
    <property name="visible">True</property>
    <property name="can_focus">False</property>
    <property name="label_xalign">0</property>
    <property name="shadow_type">in</property>
    <child>
      <object class="GtkBox" id="list">
        <property name="visible">True</property>
        <property name="can_focus">False</property>
        <property name="orientation">vertical</property>
        <child>
          <object class="GtkBox" id="row1">
            <property name="visible">True</property>
            <property name="can_focus">False</property>
            <child>
              <object class="GtkLabel" id="component_type_label">
                <property name="visible">True</property>
                <property name="can_focus">False</property>
                <property name="xpad">8</property>
                <property name="ypad">8</property>
                <property name="label" translatable="yes">Component Type</property>
                <property name="justify">right</property>
                <property name="lines">1</property>
              </object>
              <packing>
                <property name="expand">False</property>
                <property name="fill">True</property>
                <property name="position">0</property>
              </packing>
            </child>
            <child>
              <object class="GtkLabel" id="component_type">
                <property name="visible">True</property>
                <property name="can_focus">False</property>
                <property name="xpad">8</property>
                <property name="ypad">8</property>
                <property name="label" translatable="yes">placeholder</property>
                <property name="justify">center</property>
                <property name="lines">1</property>
              </object>
              <packing>
                <property name="expand">True</property>
                <property name="fill">True</property>
                <property name="position">1</property>
              </packing>
            </child>
          </object>
          <packing>
            <property name="expand">False</property>
            <property name="fill">True</property>
            <property name="position">0</property>
          </packing>
        </child>
      </object>
    </child>
    <child type="label">
      <object class="GtkLabel" id="instance_name_label">
        <property name="visible">True</property>
        <property name="can_focus">False</property>
        <property name="label" translatable="yes">Placeholder Name</property>
        <property name="lines">1</property>
      </object>
    </child>
  </object>
</interface>
